import serial
import threading
import time
from datetime import datetime
from collections import deque
import configparser
import os

# ===== 端口定义 =====
# 命名：X_IN = 外设→PC 侧（接外设板），X_OUT = PC→游戏侧（接游戏）。
# 触摸：GOPI(游戏侧) / CIPO_1P / CIPO_2P(触摸控制器)。
# 转发对(顺序即配对)：Light_IN<->Light_OUT、Camera_IN<->Camera_OUT、CARD_IN<->CARD_OUT。
PORT_NAMES = ['GOPI', 'CIPO_1P', 'CIPO_2P',
              'Light_IN', 'Light_OUT', 'Camera_IN', 'Camera_OUT',
              'CARD_IN', 'CARD_OUT']
# 透明转发配对：(外设侧, 游戏侧, 中文标签)——双向空闲分帧透传
FORWARD_PAIRS = [
    ('Light_IN', 'Light_OUT', '灯光通信'),
    ('Camera_IN', 'Camera_OUT', '摄像机通信'),
]

# 每端口默认配置：port / baud / framing(仅转发口生效) / log / idle_ms
DEFAULT_PORTS = {
    'GOPI':       {'port': 'COM34', 'baud': '9600',   'framing': '0', 'log': '1', 'idle_ms': '4'},
    'CIPO_1P':    {'port': 'COM3',  'baud': '9600',   'framing': '0', 'log': '1', 'idle_ms': '4'},
    'CIPO_2P':    {'port': '',      'baud': '9600',   'framing': '0', 'log': '1', 'idle_ms': '4'},
    'Light_IN':   {'port': 'COM21', 'baud': '115200', 'framing': '1', 'log': '1', 'idle_ms': '4'},  # 接灯光控制板
    'Light_OUT':  {'port': 'COM31', 'baud': '115200', 'framing': '1', 'log': '1', 'idle_ms': '4'},  # 接游戏灯光输出
    'Camera_IN':  {'port': 'COM32', 'baud': '115200',   'framing': '1', 'log': '1', 'idle_ms': '4'},  # 接摄像机控制板
    'Camera_OUT': {'port': 'COM33', 'baud': '115200',   'framing': '1', 'log': '1', 'idle_ms': '4'},  # 接游戏摄像机输出
    'CARD_IN':    {'port': 'COM35', 'baud': '38400',  'framing': '1', 'log': '1', 'idle_ms': '4'},  # 接读卡器(1P)
    'CARD_OUT':   {'port': 'COM36', 'baud': '38400',  'framing': '1', 'log': '1', 'idle_ms': '4',
                   'dummy_2p': '0', 'hinata': '0'},  # 接游戏读卡器侧；dummy_2p=1 软件模拟 2P 自检；hinata=1 拦截 2P 读卡应答为无卡
}
# 全局默认配置
DEFAULT_GLOBAL = {'delay_ms': '16', 'vsync_rate': '60', 'idle_ms': '4', 'loss_period': '10'}

CONFIG_FILE = "m22mt_config.ini"
LOG_DIR = "logs"

# ===== aime 读卡器协议（型号 TN32MSEC003S，详见 aime/aime指令分析.md）=====
# 应答帧：E0 长度 地址 序号 命令 状态 数据长度 [数据] 校验和；长度=逻辑帧长-2；
# 校验和=(除 E0 与校验和外所有逻辑字节之和)&0xFF；转义 E0->D0 DF、D0->D0 CF。
AIME_ADDR_2P = 0x01
# dummy_2p 需应答的 2P 自检指令：切普通模式/查固件版本/查硬件版本/设KeyB/设KeyA
AIME_DUMMY_SELFTEST_CMDS = (0x62, 0x30, 0x32, 0x54, 0x50)
AIME_CMD_START_POLL = 0x40          # 2P 轮询起始，dummy_2p 忽略（连同 41/42 等其它 2P 指令）
AIME_FW_VERSION = b'TN32MSEC003S F/W Ver1.0'   # 0x30 应答(23B)
AIME_HW_VERSION = b'TN32MSEC003S H/W Ver3.0'   # 0x32 应答(23B)
AIME_CMD_CARD_DETECT = 0x42          # 卡片检测；应答 st=00 dl=01 data=00 表示无卡
AIME_NO_CARD_DATA = b'\x00'          # 0x42 无卡应答数据（hinata 模式改写 2P 有卡应答时用）

# 默认全零状态
ALL_ZERO_STATE = bytes([
    0x28,       # Start byte '('
    0x40, 0x40, 0x40, 0x40,  # P1 bytes (A1-A8, B1-B8, C all 0)
    0x40, 0x40,  # Padding '@@'
    0x40, 0x40, 0x40, 0x40,  # P2 bytes (A1-A8, B1-B8, C all 0)
    0x40, 0x40,  # Padding '@@'
    0x29         # End byte ')'
])


def _to_bool(val, default=False):
    """把配置值解析为布尔；无法识别时返回 default"""
    s = str(val).strip().lower()
    if s in ('1', 'true', 'yes', 'on'):
        return True
    if s in ('0', 'false', 'no', 'off', ''):
        return False
    return default


def _aime_unescape(b):
    """去掉 D0 转义：D0 CF->D0，D0 DF->E0（作用于帧头 E0 之后的字节）"""
    out = bytearray()
    i = 0
    n = len(b)
    while i < n:
        if b[i] == 0xD0 and i + 1 < n:
            if b[i + 1] == 0xCF:
                out.append(0xD0); i += 2; continue
            if b[i + 1] == 0xDF:
                out.append(0xE0); i += 2; continue
        out.append(b[i]); i += 1
    return bytes(out)


def _aime_escape(b):
    """施加 D0 转义：E0->D0 DF，D0->D0 CF"""
    out = bytearray()
    for x in b:
        if x == 0xE0:
            out += b'\xD0\xDF'
        elif x == 0xD0:
            out += b'\xD0\xCF'
        else:
            out.append(x)
    return bytes(out)


def _aime_build_resp(addr, seq, cmd, status, data=b''):
    """构造一条 aime 读卡器应答帧（含长度/校验和/D0 转义），返回上线字节"""
    data = bytes(data)
    body = bytes([addr & 0xFF, seq & 0xFF, cmd & 0xFF,
                  status & 0xFF, len(data) & 0xFF]) + data
    length = (len(body) + 1) & 0xFF              # 长度字节计入自身
    chk = (length + sum(body)) & 0xFF            # 除 E0 与校验和外求和
    tail = bytes([length]) + body + bytes([chk])
    return b'\xE0' + _aime_escape(tail)


def _aime_split_frames(buf):
    """把缓冲切成若干上线帧：未转义的 E0 恒为帧起始（帧内 E0 已转义为 D0 DF）"""
    frames = []
    for part in bytes(buf).split(b'\xE0'):
        if part:
            frames.append(b'\xE0' + part)
    return frames


def _aime_parse_head(frame):
    """从上线帧解析 (addr, seq, cmd)；结构不足返回 None"""
    lg = b'\xE0' + _aime_unescape(frame[1:])
    if len(lg) < 6 or lg[0] != 0xE0:
        return None
    return lg[2], lg[3], lg[4]


def _aime_parse_resp(frame):
    """从上线应答帧解析 (addr, seq, cmd, status, data_len)；结构不足返回 None。
    应答帧比请求多一个状态字节：E0 长度 地址 序号 命令 状态 数据长度 [数据] 校验和"""
    lg = b'\xE0' + _aime_unescape(frame[1:])
    if len(lg) < 8 or lg[0] != 0xE0:
        return None
    return lg[2], lg[3], lg[4], lg[5], lg[6]


class PortLogger:
    """单个串口的收发日志器：每行 [时间] RX/TX <hex> | <ascii>，收发合并到一个文件"""

    def __init__(self, name, enabled, logdir=LOG_DIR):
        self.name = name
        self.enabled = bool(enabled)
        self._fh = None
        self._lock = threading.Lock()
        if self.enabled:
            try:
                os.makedirs(logdir, exist_ok=True)
                self._fh = open(os.path.join(logdir, f'{name}.log'), 'a', encoding='utf-8')
            except Exception as e:
                print(f"[日志] {name} 日志文件打开失败，已禁用该端口日志: {e}")
                self.enabled = False

    def log(self, direction, data):
        if not self.enabled or not data:
            return
        ts = datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')[:-3]
        hexs = data.hex(' ')
        asc = ''.join(chr(b) if 32 <= b < 127 else '.' for b in data)
        line = f'[{ts}] {direction} {hexs} | {asc}\n'
        try:
            with self._lock:
                self._fh.write(line)
                self._fh.flush()
        except Exception:
            pass

    def header(self, text):
        if self.enabled and self._fh:
            try:
                with self._lock:
                    self._fh.write(text + '\n')
                    self._fh.flush()
            except Exception:
                pass

    def close(self):
        if self._fh:
            try:
                self._fh.close()
            except Exception:
                pass
            self._fh = None


class TouchBridge:
    def __init__(self):
        self.active = False
        self.lock = threading.Lock()
        self.ports = {}          # name -> serial.Serial（仅成功打开的端口）
        self.loggers = {}        # name -> PortLogger
        self.write_locks = {n: threading.Lock() for n in PORT_NAMES}
        self.key_mappings = {}   # {"XX": bytes([Y])}

        # 加载配置
        self.config = self.load_config()
        self.gcfg = self.config['global']
        self.pcfg = self.config['ports']

        # 2P 是否启用（端口非空）
        self.enable_2p = bool(self.pcfg['CIPO_2P']['port'].strip())

        # CARD(读卡器) dummy_2p：软件模拟 2P 读卡器自检应答（配置在 CARD_OUT 段）
        self.card_dummy_2p = _to_bool(self.pcfg.get('CARD_OUT', {}).get('dummy_2p', '0'), False)
        self._dummy2p_normal_done = False   # 是否已对首个 0x62 回过 status=00（其后回 03）
        # CARD(读卡器) hinata：Hinata 兼容读卡器单台同时应答 1P/2P，读卡时会把同一张卡
        # 也上报给 2P(addr=0x01) 致其卡在登录确认；开启后把 2P 的 0x42 有卡应答改写为无卡
        self.card_hinata = _to_bool(self.pcfg.get('CARD_OUT', {}).get('hinata', '0'), False)

        # 全局参数
        self.delay_ms = self._to_int(self.gcfg['delay_ms'], 16, '延迟')
        if self.delay_ms < 0:
            print("延迟时间不能为负数，使用默认值16ms")
            self.delay_ms = 16
        elif self.delay_ms > 100:
            print("警告：延迟时间超过100ms，可能会影响游戏体验")

        self.vsync_rate = self._to_int(self.gcfg['vsync_rate'], 60, '垂直同步频率')
        if self.vsync_rate <= 0:
            print("垂直同步频率必须大于0，使用默认值60Hz")
            self.vsync_rate = 60
        elif self.vsync_rate > 1000:
            print("警告：垂直同步频率超过1000Hz，可能会影响性能")
        self.vsync_interval = 1.0 / self.vsync_rate

        # 9600 波特率下 14 字节触摸包(8N1=10bit/字节)理论上限：baud/(包长×10)
        # 例 9600 → 68.5 包/秒；60Hz 时占 840/960≈87.5% 带宽，可行但余量不大
        try:
            _gopi_baud = int(str(self.pcfg['GOPI']['baud']).strip())
            _max_rate = _gopi_baud / (len(ALL_ZERO_STATE) * 10)
            if self.vsync_rate > _max_rate:
                print(f"警告：vsync_rate={self.vsync_rate}Hz 超过 {_gopi_baud} 波特下 "
                      f"{len(ALL_ZERO_STATE)} 字节包的理论上限 {_max_rate:.1f}Hz，将无法稳定达标")
        except Exception:
            pass

        self.loss_period = self._to_int(self.gcfg['loss_period'], 10, '丢包统计周期')
        if self.loss_period <= 0:
            self.loss_period = 10
        self.default_idle_ms = self._to_int(self.gcfg['idle_ms'], 4, '空闲分帧阈值')
        if self.default_idle_ms < 0:
            self.default_idle_ms = 4

        # 触摸数据状态
        self.delayed_buffer_1p = deque()
        self.delayed_buffer_2p = deque()
        self.last_state = ALL_ZERO_STATE
        self.latest_1p_data = None
        self.latest_2p_data = None

        # 丢包率统计（当前周期内）
        self.period_send_count = 0
        self.period_active_time = 0.0

    # ---------- 工具 ----------
    def _to_int(self, val, default, what):
        try:
            return int(str(val).strip())
        except (ValueError, TypeError):
            print(f"{what}配置无效({val})，使用默认值{default}")
            return default

    def log_port(self, name, direction, data):
        lg = self.loggers.get(name)
        if lg:
            lg.log(direction, data)

    def port_write(self, name, data):
        """向指定端口写数据并记录 TX 日志（线程安全）"""
        ser = self.ports.get(name)
        if ser is None:
            return False
        try:
            with self.write_locks[name]:
                ser.write(data)
            self.log_port(name, 'TX', data)
            return True
        except Exception as e:
            print(f"[串口写入] {name} 失败: {e}")
            return False

    # ---------- 配置 ----------
    def load_config(self):
        """加载每端口 section 配置；文件缺失或损坏时回退默认并生成默认文件"""
        defaults = {'global': dict(DEFAULT_GLOBAL),
                    'ports': {k: dict(v) for k, v in DEFAULT_PORTS.items()}}
        if not os.path.exists(CONFIG_FILE):
            self._write_default_config(CONFIG_FILE)
            print(f"未找到 {CONFIG_FILE}，已生成含各端口 section 的默认配置，请按需修改后重新运行")
            return defaults
        config = configparser.ConfigParser()
        try:
            config.read(CONFIG_FILE, encoding='utf-8')
        except Exception as e:
            print(f"读取配置文件失败: {e}，使用默认配置")
            return defaults
        g = {k: config.get('global', k, fallback=dv) for k, dv in DEFAULT_GLOBAL.items()}
        ports = {}
        for name in PORT_NAMES:
            d = dict(DEFAULT_PORTS[name])
            if config.has_section(name):
                for k in d:
                    # 兼容旧配置：framing 行内注释(如 "1 ; ...")只取首 token
                    raw = config.get(name, k, fallback=d[k])
                    d[k] = raw.split(';', 1)[0].strip() if k != 'port' else raw
            ports[name] = d
        print("配置文件加载成功")
        return {'global': g, 'ports': ports}

    def _write_default_config(self, path):
        comments = {
            'GOPI': '游戏侧串口（接收命令 / 回传触摸状态）',
            'CIPO_1P': '1P 触摸控制器串口',
            'CIPO_2P': '2P 触摸控制器串口（port 留空则禁用 2P）',
            'Light_IN': '灯光 外设→PC：接灯光控制板',
            'Light_OUT': '灯光 PC→游戏：接游戏灯光输出',
            'Camera_IN': '摄像机 外设→PC：接摄像机控制板',
            'Camera_OUT': '摄像机 PC→游戏：接游戏摄像机输出',
            'CARD_IN': '读卡器 外设→PC：接读卡器(1P)',
            'CARD_OUT': '读卡器 PC→游戏：接游戏读卡器侧（dummy_2p 在此拦截 2P 自检）',
        }
        L = []
        L.append('[global]')
        L.append('; 触摸输入延迟(ms)')
        L.append(f'delay_ms = {DEFAULT_GLOBAL["delay_ms"]}')
        L.append('; 垂直同步发送频率(Hz)')
        L.append(f'vsync_rate = {DEFAULT_GLOBAL["vsync_rate"]}')
        L.append('; 空闲分帧默认阈值(ms)：端口未单独设 idle_ms 时使用')
        L.append(f'idle_ms = {DEFAULT_GLOBAL["idle_ms"]}')
        L.append('; 丢包率统计周期(秒)，每周期结束仅在丢包率>0时打印一行')
        L.append(f'loss_period = {DEFAULT_GLOBAL["loss_period"]}')
        L.append('')
        for name in PORT_NAMES:
            d = DEFAULT_PORTS[name]
            L.append(f'[{name}]')
            L.append(f'; {comments[name]}')
            L.append('; port 留空则停用该端口/该组转发')
            L.append(f'port = {d["port"]}')
            L.append(f'baud = {d["baud"]}')
            L.append('; framing 仅对转发口(Light/Camera/CARD)生效：1=按空闲分帧整条转发，0=即时透传；触摸口忽略')
            L.append(f'framing = {d["framing"]}')
            L.append(f'; log：1=记录该端口收发到 {LOG_DIR}/{name}.log，0=不记录')
            L.append(f'log = {d["log"]}')
            L.append('; idle_ms：空闲分帧阈值(ms)，超过该空闲即认为一帧结束')
            L.append(f'idle_ms = {d["idle_ms"]}')
            if 'dummy_2p' in d:
                L.append('; dummy_2p：1=软件模拟 2P 读卡器——对游戏发往 addr=0x01 的自检指令')
                L.append(';           (0x62/0x30/0x32/0x54/0x50)合成应答，对 0x40 轮询等其余 2P 指令忽略；')
                L.append(';           用于只接 1P 读卡器时让游戏自检通过。0=关闭(透明转发)')
                L.append(f'dummy_2p = {d["dummy_2p"]}')
            if 'hinata' in d:
                L.append('; hinata：1=Hinata 兼容读卡器模式——该读卡器单台同时应答 1P(0x00)/2P(0x01)，读卡时')
                L.append(';         把同一张卡也上报给 2P，导致 2P 卡在登录确认。开启后拦截读卡器对 addr=0x01')
                L.append(';         的 0x42(卡片检测)有卡应答、改写为无卡，使 2P 不再触发登录。仅 framing=1 生效；')
                L.append(';         与 dummy_2p 用途不同(此为真实 Hinata 读卡器)，一般二选一。0=关闭')
                L.append(f'hinata = {d["hinata"]}')
            L.append('')
        with open(path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(L))

    def setup_loggers(self):
        for name in PORT_NAMES:
            enabled = _to_bool(self.pcfg[name]['log'], False)
            self.loggers[name] = PortLogger(name, enabled)

    # ---------- 串口打开 ----------
    def _open_serial(self, port, baud, desc):
        """打开串口；被占用/不存在/失败时打印清晰提示并返回 None"""
        try:
            return serial.Serial(port, baud, timeout=0.1)
        except serial.SerialException as e:
            msg = str(e)
            low = msg.lower()
            if ('permission' in low or 'access is denied' in low
                    or 'being used by another process' in low or 'errno 13' in low):
                print(f"[串口占用] {desc} 端口 {port} 已被其他程序占用，无法打开：{msg}")
            elif ('filenotfound' in low or 'no such file' in low
                  or 'does not exist' in low or 'errno 2' in low):
                print(f"[串口错误] {desc} 端口 {port} 不存在，请检查端口号：{msg}")
            else:
                print(f"[串口错误] {desc} 端口 {port} 打开失败：{msg}")
            return None
        except OSError as e:
            if getattr(e, 'errno', None) == 13:
                print(f"[串口占用] {desc} 端口 {port} 已被其他程序占用，无法打开：{e}")
            else:
                print(f"[串口错误] {desc} 端口 {port} 打开失败：{e}")
            return None

    def open_port(self, name, desc):
        """按配置打开指定端口并登记到 self.ports；未配置或失败返回 None"""
        cfg = self.pcfg[name]
        port = cfg['port'].strip()
        if not port:
            return None
        baud = self._to_int(cfg['baud'], 9600, f'{name} 波特率')
        ser = self._open_serial(port, baud, desc)
        if ser is not None:
            self.ports[name] = ser
        return ser

    # ---------- 触摸数据变换（保持不变） ----------
    def transform_touch_data_1p(self, raw_data):
        """
        将mai2格式的触摸数据转换为mai格式 (1P)
        输入: mai2格式的bytes (9字节，以b'\x28'开头，b'\x29'结尾)
        输出: mai格式的bytes (14字节，以b'\x28'开头，b'\x29'结尾)
        """
        # 验证输入数据
        if len(raw_data) != 9 or raw_data[0] != 0x28 or raw_data[8] != 0x29:
            raise ValueError("Invalid mai2 input data format")
    
        # 初始化mai输出数据 (全初始化为0x40 '@')
        mai_data = [0x40] * 14
        mai_data[0] = 0x28  # 起始字节 '('
        mai_data[13] = 0x29  # 结束字节 ')'
    
        # mai2到mai的映射关系 (mai2区域 -> mai字节/位) - 1P
        zone_mapping = {
            # A区映射 (P1)
            'A1': (1, 0), 'A2': (1, 2), 'A3': (2, 0), 'A4': (2, 2),
            'A5': (3, 0), 'A6': (3, 2), 'A7': (4, 0), 'A8': (4, 2),
            # B区映射 (P1)
            'B1': (1, 1), 'B2': (1, 3), 'B3': (2, 1), 'B4': (2, 3),
            'B5': (3, 1), 'B6': (3, 3), 'B7': (4, 1), 'B8': (4, 3),
            # C区映射 (合并C1和C2)
            'C1': (4, 4), 'C2': (4, 4)  # 两者都映射到同一位
        }
    
        # mai2的区域定义 (字节位置, 位位置): 区域名称
        mai2_zones = {
            # A区
            (1, 0): 'A1', (1, 1): 'A2', (1, 2): 'A3', (1, 3): 'A4',
            (1, 4): 'A5', (2, 0): 'A6', (2, 1): 'A7', (2, 2): 'A8',
            # B区
            (2, 3): 'B1', (2, 4): 'B2', (3, 0): 'B3', (3, 1): 'B4',
            (3, 2): 'B5', (3, 3): 'B6', (3, 4): 'B7', (4, 0): 'B8',
            # C区
            (4, 1): 'C1', (4, 2): 'C2'
        }
    
        # 处理mai2数据中的每个区域
        for byte_pos in range(1, 8):  # 只处理字节1-7
            byte = raw_data[byte_pos]
            for bit_pos in range(8):
                if byte & (1 << bit_pos):
                    zone = mai2_zones.get((byte_pos, bit_pos))
                    if zone in zone_mapping:
                        mai_byte, mai_bit = zone_mapping[zone]
                        mai_data[mai_byte] |= (1 << mai_bit)
    
        return bytes(mai_data)

    def transform_touch_data_2p(self, raw_data):
        """
        将mai2格式的触摸数据转换为mai格式 (2P)
        输入: mai2格式的bytes (9字节，以b'\x28'开头，b'\x29'结尾)
        输出: mai格式的bytes (14字节，以b'\x28'开头，b'\x29'结尾)
        """
        # 验证输入数据
        if len(raw_data) != 9 or raw_data[0] != 0x28 or raw_data[8] != 0x29:
            raise ValueError("Invalid mai2 input data format")
    
        # 初始化mai输出数据 (全初始化为0x40 '@')
        mai_data = [0x40] * 14
        mai_data[0] = 0x28  # 起始字节 '('
        mai_data[13] = 0x29  # 结束字节 ')'
    
        # mai2到mai的映射关系 (mai2区域 -> mai字节/位) - 2P
        zone_mapping = {
            # A区映射 (P2)
            'A1': (7, 0), 'A2': (7, 2), 'A3': (8, 0), 'A4': (8, 2),
            'A5': (9, 0), 'A6': (9, 2), 'A7': (10, 0), 'A8': (10, 2),
            # B区映射 (P2)
            'B1': (7, 1), 'B2': (7, 3), 'B3': (8, 1), 'B4': (8, 3),
            'B5': (9, 1), 'B6': (9, 3), 'B7': (10, 1), 'B8': (10, 3),
            # C区映射 (合并C1和C2)
            'C1': (10, 4), 'C2': (10, 4)  # 两者都映射到同一位
        }
    
        # mai2的区域定义 (字节位置, 位位置): 区域名称
        mai2_zones = {
            # A区
            (1, 0): 'A1', (1, 1): 'A2', (1, 2): 'A3', (1, 3): 'A4',
            (1, 4): 'A5', (2, 0): 'A6', (2, 1): 'A7', (2, 2): 'A8',
            # B区
            (2, 3): 'B1', (2, 4): 'B2', (3, 0): 'B3', (3, 1): 'B4',
            (3, 2): 'B5', (3, 3): 'B6', (3, 4): 'B7', (4, 0): 'B8',
            # C区
            (4, 1): 'C1', (4, 2): 'C2'
        }
    
        # 处理mai2数据中的每个区域
        for byte_pos in range(1, 8):  # 只处理字节1-7
            byte = raw_data[byte_pos]
            for bit_pos in range(8):
                if byte & (1 << bit_pos):
                    zone = mai2_zones.get((byte_pos, bit_pos))
                    if zone in zone_mapping:
                        mai_byte, mai_bit = zone_mapping[zone]
                        mai_data[mai_byte] |= (1 << mai_bit)
    
        return bytes(mai_data)

    def combine_1p_2p_data(self, data_1p, data_2p):
        """
        合并1P和2P的数据
        如果只有1P数据，返回1P数据
        如果有2P数据，合并1P和2P数据
        """
        if data_2p is None:
            return data_1p
        
        # 将1P和2P数据合并
        combined_data = bytearray(data_1p)
        
        # 将2P数据复制到对应位置 (字节7-10)
        for i in range(4):
            combined_data[7 + i] = data_2p[7 + i]
        
        return bytes(combined_data)

    # ---------- GOPI 命令处理 ----------
    def handle_GOPI_to_CIPO(self):
        """游戏侧 -> 触摸控制器。

        串口可能逐字节到达，先累积再按 {...} 完整帧提取处理，避免命令被拆散。
        """
        buffer = bytearray()
        while True:
            try:
                ser = self.ports.get('GOPI')
                if ser is None:
                    time.sleep(0.5)
                    continue
                waiting = ser.in_waiting
                if waiting > 0:
                    data = ser.read(waiting)
                    if data:
                        self.log_port('GOPI', 'RX', data)
                    buffer.extend(data)
                    while True:
                        start = buffer.find(b'{')
                        if start == -1:
                            buffer.clear()
                            break
                        end = buffer.find(b'}', start + 1)
                        if end == -1:
                            if start > 0:
                                del buffer[:start]
                            break
                        frame = bytes(buffer[start:end + 1])
                        del buffer[:end + 1]
                        self.process_gopi_frame(frame)
                else:
                    time.sleep(0.001)
            except Exception as e:
                print(f"Error in GOPI handler: {e}")
                time.sleep(1)

    def process_gopi_frame(self, data):
        """处理一个完整的 GOPI 命令帧（已保证为 {...} 形式）"""
        # {XXkY}：建立映射关系
        if len(data) == 6 and data.startswith(b'{') and data.endswith(b'}'):
            if data[3] == ord('k'):
                prefix = data[1:3].decode('ascii', 'replace')
                suffix = data[4:5]
                self.key_mappings[prefix] = suffix
                response = b'(' + data[1:3] + b'  )'
                self.port_write('GOPI', response)
                print(f"注册映射: {prefix} -> {suffix}")
                return
            # {XXth}：查询映射
            if data[3:5] == b'th':
                prefix = data[1:3].decode('ascii', 'replace')
                if prefix in self.key_mappings:
                    y_value = self.key_mappings[prefix]
                    response = b'(' + data[1:3] + b' ' + y_value + b')'
                    self.port_write('GOPI', response)
                return

        # 标准命令
        if b'{STAT}' in data:
            with self.lock:
                self.active = True
                self.last_state = ALL_ZERO_STATE
            self.port_write('GOPI', ALL_ZERO_STATE)
            self.port_write('CIPO_1P', b'{STAT}')
            if self.enable_2p:
                self.port_write('CIPO_2P', b'{STAT}')
            print("GOPI 激活 (STAT)")
        elif b'{HALT}' in data:
            with self.lock:
                self.active = False
            self.port_write('CIPO_1P', b'{HALT}')
            if self.enable_2p:
                self.port_write('CIPO_2P', b'{HALT}')
            print("GOPI 停止 (HALT)")

    # ---------- 触摸控制器 -> 游戏 ----------
    def handle_CIPO_to_GOPI_1p(self):
        """1P 触摸控制器 -> 游戏（带垂直同步发送与丢包统计）"""
        last_loop = time.time()
        next_vsync = time.time()
        while True:
            try:
                # 累计活跃时间（用于丢包率：期望发送 = 活跃时间 × vsync_rate）
                now0 = time.time()
                dt = now0 - last_loop
                last_loop = now0
                if self.active and 0 <= dt < 1.0:
                    with self.lock:
                        self.period_active_time += dt

                ser = self.ports.get('CIPO_1P')
                if ser and ser.in_waiting > 0:
                    data = ser.read(ser.in_waiting)
                    if data:
                        self.log_port('CIPO_1P', 'RX', data)
                        if data.startswith(b'\x28') and data.endswith(b'\x29'):
                            if len(data) == 9:
                                self.latest_1p_data = data
                            elif len(data) > 9:
                                for packet in data.split(b'\x29'):
                                    if len(packet) >= 8:
                                        full_packet = packet + b'\x29'
                                        if len(full_packet) == 9:
                                            self.latest_1p_data = full_packet
                        elif data in (b'{STAT}', b'{HALT}'):
                            self.port_write('GOPI', data)

                # 垂直同步：按固定频率发送
                current_time = time.time()
                if current_time >= next_vsync:
                    if self.active and self.latest_1p_data:
                        delayed_time = current_time + (self.delay_ms / 1000)
                        with self.lock:
                            self.delayed_buffer_1p.append((self.latest_1p_data, delayed_time))

                    with self.lock:
                        while self.delayed_buffer_1p:
                            delayed_data, release_time = self.delayed_buffer_1p[0]
                            if current_time >= release_time:
                                self.delayed_buffer_1p.popleft()
                                if self.active:
                                    try:
                                        transformed_1p = self.transform_touch_data_1p(delayed_data)
                                        if self.enable_2p and self.latest_2p_data:
                                            transformed_2p = self.transform_touch_data_2p(self.latest_2p_data)
                                            combined_data = self.combine_1p_2p_data(transformed_1p, transformed_2p)
                                        else:
                                            combined_data = transformed_1p
                                        self.port_write('GOPI', combined_data)
                                        self.last_state = combined_data
                                        self.period_send_count += 1
                                    except Exception as e:
                                        print(f"Error transforming 1P data: {e}")
                            else:
                                break
                    # 绝对时间栅格推进，过冲不再累积（避免实际频率系统性低于 vsync_rate）
                    next_vsync += self.vsync_interval
                    if next_vsync <= current_time:
                        # 落后过多（阻塞/卡顿），跳过补偿、重新对齐，避免爆发式补发
                        next_vsync = current_time + self.vsync_interval

                time.sleep(0.0001)
            except Exception as e:
                print(f"Error in CIPO 1P handler: {e}")
                time.sleep(1)

    def handle_CIPO_to_GOPI_2p(self):
        """2P 触摸控制器 -> 游戏"""
        if not self.enable_2p or 'CIPO_2P' not in self.ports:
            return
        while True:
            try:
                ser = self.ports.get('CIPO_2P')
                if ser and ser.in_waiting > 0:
                    data = ser.read(ser.in_waiting)
                    if data:
                        self.log_port('CIPO_2P', 'RX', data)
                        if data.startswith(b'\x28') and data.endswith(b'\x29'):
                            if len(data) == 9:
                                self.latest_2p_data = data
                            elif len(data) > 9:
                                for packet in data.split(b'\x29'):
                                    if len(packet) >= 8:
                                        full_packet = packet + b'\x29'
                                        if len(full_packet) == 9:
                                            self.latest_2p_data = full_packet
                        elif data in (b'{STAT}', b'{HALT}'):
                            self.port_write('GOPI', data)
                time.sleep(0.001)
            except Exception as e:
                print(f"Error in CIPO 2P handler: {e}")
                time.sleep(1)

    # ---------- 外围设备指令转发（空闲分帧） ----------
    def handle_forward(self, src_name, dst_name, label):
        """将 src 收到的数据转发到 dst。

        framing 开启时：累积字节，超过 idle_ms 空闲即认为一帧结束，整帧一次写出，
        使字节在 UART 上连续发出（等效直接跳线），解决逐字节交付导致的“一字一停”。
        framing 关闭时：即时透传（收到即转发）。
        透明转发，不改写任何字节内容。
        """
        scfg = self.pcfg[src_name]
        framing = _to_bool(scfg['framing'], True)
        idle_ms = self._to_int(scfg['idle_ms'], self.default_idle_ms, f'{src_name} idle_ms')
        idle = max(0.0, idle_ms / 1000.0)
        src = self.ports.get(src_name)
        dst = self.ports.get(dst_name)
        if src is None or dst is None:
            return
        buf = bytearray()
        last_rx = 0.0
        while True:
            try:
                now = time.time()
                waiting = src.in_waiting
                if waiting > 0:
                    data = src.read(waiting)
                    if data:
                        self.log_port(src_name, 'RX', data)
                        if framing:
                            buf.extend(data)
                            last_rx = time.time()
                        else:
                            dst.write(data)
                            self.log_port(dst_name, 'TX', data)
                else:
                    if framing and buf and (now - last_rx) >= idle:
                        frame = bytes(buf)
                        buf.clear()
                        dst.write(frame)
                        self.log_port(dst_name, 'TX', frame)
                    else:
                        time.sleep(0.001)
            except Exception as e:
                print(f"[外围设备指令转发] {label} 错误: {e}")
                time.sleep(1)

    def setup_peripheral_forwarding(self):
        """按配置打开转发端口并启动各组双向转发线程"""
        for a_name, b_name, label in FORWARD_PAIRS:
            pa = self.pcfg[a_name]['port'].strip()
            pb = self.pcfg[b_name]['port'].strip()
            if not pa or not pb:
                print(f"[转发-{label}] {a_name}/{b_name} 端口未配置完整，跳过该组")
                continue
            ser_a = self.open_port(a_name, f'{label}-A')
            if ser_a is None:
                print(f"[转发-{label}] {pa} 不可用（可能已被占用），跳过该组")
                continue
            ser_b = self.open_port(b_name, f'{label}-B')
            if ser_b is None:
                print(f"[转发-{label}] {pb} 不可用（可能已被占用），跳过该组")
                try:
                    ser_a.close()
                except Exception:
                    pass
                self.ports.pop(a_name, None)
                continue
            fa = _to_bool(self.pcfg[a_name]['framing'], True)
            fb = _to_bool(self.pcfg[b_name]['framing'], True)
            threading.Thread(target=self.handle_forward,
                             args=(a_name, b_name, f'{label} {pa}->{pb}'), daemon=True).start()
            threading.Thread(target=self.handle_forward,
                             args=(b_name, a_name, f'{label} {pb}->{pa}'), daemon=True).start()
            print(f"[转发-{label}] 已启动: {pa} <-> {pb}（分帧 {a_name}:{'开' if fa else '关'} / {b_name}:{'开' if fb else '关'}）")

    # ---------- 读卡器(CARD)转发 + dummy_2p ----------
    def _dummy_2p_response(self, seq, cmd):
        """为 2P(addr=0x01) 自检指令合成应答帧；非自检指令(如 0x40 轮询)返回 None(忽略)"""
        a = AIME_ADDR_2P
        if cmd == 0x62:                       # TO_NORMAL：首次 00，其后 03（与真实读卡器一致）
            if not self._dummy2p_normal_done:
                self._dummy2p_normal_done = True
                return _aime_build_resp(a, seq, cmd, 0x00)
            return _aime_build_resp(a, seq, cmd, 0x03)
        if cmd == 0x30:                       # GET_FW_VERSION
            return _aime_build_resp(a, seq, cmd, 0x00, AIME_FW_VERSION)
        if cmd == 0x32:                       # GET_HW_VERSION
            return _aime_build_resp(a, seq, cmd, 0x00, AIME_HW_VERSION)
        if cmd in (0x54, 0x50):               # KEY_SET_B / KEY_SET_A
            return _aime_build_resp(a, seq, cmd, 0x00)
        return None                           # 0x40 及其余 2P 指令一律忽略

    def _process_card_game_frame(self, frame):
        """处理 CARD_OUT(游戏侧)收到的一帧：dummy_2p 拦截 addr=0x01，其余转发到 CARD_IN"""
        if not self.card_dummy_2p:
            self.port_write('CARD_IN', frame)
            return
        fwd = bytearray()
        for fw in _aime_split_frames(frame):
            head = _aime_parse_head(fw)
            if head is not None and head[0] == AIME_ADDR_2P:
                resp = self._dummy_2p_response(head[1], head[2])
                if resp:
                    self.port_write('CARD_OUT', resp)   # 合成 2P 应答回游戏
                continue                                # 2P 帧不转发给读卡器
            fwd += fw                                   # 其余(1P/灯光板等)转发给读卡器
        if fwd:
            self.port_write('CARD_IN', bytes(fwd))

    def handle_card_game_side(self):
        """CARD_OUT(游戏侧) -> CARD_IN(读卡器侧)，含 dummy_2p 拦截。按空闲分帧取整帧后处理。"""
        src_name, dst_name = 'CARD_OUT', 'CARD_IN'
        scfg = self.pcfg[src_name]
        framing = _to_bool(scfg['framing'], True)
        idle_ms = self._to_int(scfg['idle_ms'], self.default_idle_ms, f'{src_name} idle_ms')
        idle = max(0.0, idle_ms / 1000.0)
        src = self.ports.get(src_name)
        if src is None or self.ports.get(dst_name) is None:
            return
        buf = bytearray()
        last_rx = 0.0
        while True:
            try:
                now = time.time()
                waiting = src.in_waiting
                if waiting > 0:
                    data = src.read(waiting)
                    if data:
                        self.log_port(src_name, 'RX', data)
                        if framing:
                            buf.extend(data)
                            last_rx = time.time()
                        else:
                            # 不分帧时无法可靠解析，dummy_2p 仅在分帧下生效，此处直接透传
                            self.port_write(dst_name, data)
                else:
                    if framing and buf and (now - last_rx) >= idle:
                        frame = bytes(buf)
                        buf.clear()
                        self._process_card_game_frame(frame)
                    else:
                        time.sleep(0.001)
            except Exception as e:
                print(f"[读卡器转发] 游戏侧错误: {e}")
                time.sleep(1)

    def _hinata_2p_no_card(self, seq):
        """构造 addr=0x01(2P) 的 0x42 无卡应答（保留原包序号），供 hinata 模式改写用"""
        return _aime_build_resp(AIME_ADDR_2P, seq, AIME_CMD_CARD_DETECT, 0x00, AIME_NO_CARD_DATA)

    def _process_card_reader_frame(self, frame):
        """处理 CARD_IN(读卡器侧)收到的一帧应答后转发到 CARD_OUT(游戏侧)。
        hinata 模式：把 2P(addr=0x01) 的 0x42 有卡应答(data_len>1)改写为"无卡"，避免
        Hinata 单台设备把同一张卡同时上报 1P/2P 导致 2P 卡在登录确认；其余帧透明转发。"""
        if not self.card_hinata:
            self.port_write('CARD_OUT', frame)
            return
        out = bytearray()
        for fw in _aime_split_frames(frame):
            resp = _aime_parse_resp(fw)   # (addr, seq, cmd, status, data_len)
            if (resp is not None and resp[0] == AIME_ADDR_2P
                    and resp[2] == AIME_CMD_CARD_DETECT and resp[4] > 1):
                out += self._hinata_2p_no_card(resp[1])   # 2P 有卡→无卡(保留序号)
                continue
            out += fw                                      # 其余(1P卡片/无卡/预热/其它命令)原样转发
        if out:
            self.port_write('CARD_OUT', bytes(out))

    def handle_card_reader_side(self):
        """CARD_IN(读卡器侧) -> CARD_OUT(游戏侧)：转发读卡器应答回游戏（hinata 模式下把 2P 读卡应答改写为无卡）。"""
        src_name, dst_name = 'CARD_IN', 'CARD_OUT'
        scfg = self.pcfg[src_name]
        framing = _to_bool(scfg['framing'], True)
        idle_ms = self._to_int(scfg['idle_ms'], self.default_idle_ms, f'{src_name} idle_ms')
        idle = max(0.0, idle_ms / 1000.0)
        src = self.ports.get(src_name)
        if src is None or self.ports.get(dst_name) is None:
            return
        buf = bytearray()
        last_rx = 0.0
        while True:
            try:
                now = time.time()
                waiting = src.in_waiting
                if waiting > 0:
                    data = src.read(waiting)
                    if data:
                        self.log_port(src_name, 'RX', data)
                        if framing:
                            buf.extend(data)
                            last_rx = time.time()
                        else:
                            self.port_write(dst_name, data)
                else:
                    if framing and buf and (now - last_rx) >= idle:
                        frame = bytes(buf)
                        buf.clear()
                        self._process_card_reader_frame(frame)
                    else:
                        time.sleep(0.001)
            except Exception as e:
                print(f"[读卡器转发] 读卡器侧错误: {e}")
                time.sleep(1)

    def setup_card_forwarding(self):
        """打开 CARD_IN/CARD_OUT 并启动读卡器转发（含 dummy_2p）；任一为空则停用该组"""
        in_name, out_name = 'CARD_IN', 'CARD_OUT'
        p_in = self.pcfg[in_name]['port'].strip()
        p_out = self.pcfg[out_name]['port'].strip()
        if not p_in or not p_out:
            print(f"[转发-读卡器] {in_name}/{out_name} 端口未配置完整，停用该组转发")
            return
        if self.open_port(out_name, '读卡器-游戏侧') is None:
            print(f"[转发-读卡器] {p_out} 不可用（可能已被占用），跳过该组")
            return
        if self.open_port(in_name, '读卡器-读卡器侧') is None:
            print(f"[转发-读卡器] {p_in} 不可用（可能已被占用），跳过该组")
            try:
                self.ports[out_name].close()
            except Exception:
                pass
            self.ports.pop(out_name, None)
            return
        threading.Thread(target=self.handle_card_game_side, daemon=True).start()
        threading.Thread(target=self.handle_card_reader_side, daemon=True).start()
        print(f"[转发-读卡器] 已启动: {p_in}(读卡器) <-> {p_out}(游戏)  "
              f"dummy_2p={'开' if self.card_dummy_2p else '关'}  "
              f"hinata={'开' if self.card_hinata else '关'}")

    # ---------- 丢包率统计 ----------
    def stats_loop(self):
        """每 loss_period 秒统计上一周期触摸发送丢包率；仅当丢包率>0时打印一行"""
        period = self.loss_period
        while True:
            time.sleep(period)
            with self.lock:
                actual = self.period_send_count
                active_t = self.period_active_time
                self.period_send_count = 0
                self.period_active_time = 0.0
            expected = active_t * self.vsync_rate
            if expected > 0:
                deficit = expected - actual
                # 容忍 ≤1 个包的启动/周期边界抖动，避免把非丢包的节拍误差报成丢包
                if deficit > 1:
                    loss = deficit / expected
                    print(f"[发送频率] 近{period}s 丢包率 {loss * 100:.1f}%（期望≈{expected:.0f}，实际{actual}）")

    # ---------- 启动 / 收尾 ----------
    def _print_startup(self):
        print("=" * 56)
        print(f"触摸桥接启动 @ {datetime.now()}")
        print(f"  全局: 延迟={self.delay_ms}ms, vsync={self.vsync_rate}Hz, "
              f"默认空闲阈值={self.default_idle_ms}ms, 丢包统计周期={self.loss_period}s")
        for name in PORT_NAMES:
            cfg = self.pcfg[name]
            ser = self.ports.get(name)
            status = ser.name if ser else ('未配置' if not cfg['port'].strip() else '未打开')
            lg = self.loggers.get(name)
            log_txt = '日志开' if (lg and lg.enabled) else '日志关'
            extra = ''
            if name.startswith(('Light', 'Camera', 'CARD')):
                extra = (f", 分帧={'开' if _to_bool(cfg['framing'], True) else '关'}"
                         f", 空闲={cfg['idle_ms']}ms")
                if name == 'CARD_OUT':
                    extra += (f", dummy_2p={'开' if self.card_dummy_2p else '关'}"
                              f", hinata={'开' if self.card_hinata else '关'}")
            print(f"  {name:<10} {status:<8} @ {cfg['baud']:<7} {log_txt}{extra}")
        print("  2P 触摸启用: " + str(self.enable_2p))
        print("  命令: {STAT}激活 / {HALT}停止 / {XXkY}注册映射 / {XXth}查询映射")
        print("=" * 56)

    def _log_session_headers(self):
        head = f"===== 会话开始 {datetime.now()} ====="
        for name in PORT_NAMES:
            lg = self.loggers.get(name)
            if lg:
                cfg = self.pcfg[name]
                lg.header(f"{head} port={cfg['port']} baud={cfg['baud']}")

    def _close_all(self):
        for ser in list(self.ports.values()):
            try:
                ser.close()
            except Exception:
                pass
        for lg in self.loggers.values():
            try:
                lg.close()
            except Exception:
                pass

    def run(self):
        try:
            self.setup_loggers()

            if self.open_port('GOPI', 'GOPI(游戏侧)') is None:
                print("GOPI 端口无法打开，程序退出。请确认端口未被占用且端口号正确。")
                self._close_all()
                return
            if self.open_port('CIPO_1P', 'CIPO_1P(1P触摸)') is None:
                print("CIPO_1P 端口无法打开，程序退出。请确认端口未被占用且端口号正确。")
                self._close_all()
                return
            if self.enable_2p:
                if self.open_port('CIPO_2P', 'CIPO_2P(2P触摸)') is None:
                    print("2P 端口不可用，仅使用 1P 继续。")
                    self.enable_2p = False

            self.setup_peripheral_forwarding()
            self.setup_card_forwarding()
            self._print_startup()
            self._log_session_headers()

            threading.Thread(target=self.handle_GOPI_to_CIPO, daemon=True).start()
            threading.Thread(target=self.handle_CIPO_to_GOPI_1p, daemon=True).start()
            if self.enable_2p:
                threading.Thread(target=self.handle_CIPO_to_GOPI_2p, daemon=True).start()
            threading.Thread(target=self.stats_loop, daemon=True).start()

            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            print("\n正在停止触摸桥接...")
        except Exception as e:
            print(f"Error: {e}")
        finally:
            self._close_all()


if __name__ == "__main__":
    TouchBridge().run()
