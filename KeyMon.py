import atexit
import ctypes
import math
import random
import threading
import traceback
from collections.abc import Callable
from dataclasses import dataclass, field
from enum import Enum
from functools import lru_cache
from itertools import accumulate, islice, product
from queue import Queue
from typing import Any, cast

import pyglet
import pyllkb  # WFLing-Seaer/pyllkb
from pyglet.gl import glClearColor
from pyglet.graphics import Batch
from pyglet.shapes import Line
from pyglet.text import Label

# region Settings
# 配置
S_LINE_ACTIVE_TIME = 3.0  # 超过此超时的行将被固化到历史记录。秒
S_HISTORY_TTL = 10.0  # 历史记录留存时间。秒
S_MAX_HISTORY_LINES = 8  # 最大历史行数。行
S_MIN_COMBO = 2  # 最小折叠连击数。次
# 样式
S_FONT_FAMILY = ["Nishiki-teki"]  # 字体家族。推荐使用Nishiki-teki（对特殊符号支持较好）
S_FONT_SIZE = 36  # 主字体大小。磅
S_COMBO_FONT_SIZE_SCALE = 0.7  # 连击字体的大小比例。
S_LINE_HEIGHT = 56  # 行高。像素
S_MARGIN_R = 20  # 右边距。像素
S_MARGIN_D = -240  # 下边距，负值表示从屏幕顶部向下的上边距。当为负值时建议把HISTORY_GO_UPWARDS设成True。像素
S_UNDERLINE_MARGIN_L = 5  # 新修饰键下划线左边距。像素
S_UNDERLINE_MARGIN_U = 10  # 下划线基础上边距。像素
S_UNDERLINE_SPACING = 4  # 下划线间距。像素
S_HISTORY_GO_UPWARDS = True  # 历史行移动方向。True向上False向下
S_COLOR_PRESSING = (204, 128, 204, 192)  # 按下的键的颜色。RGBA
S_COLOR_NORMAL = (128, 204, 204, 192)  # 松开的键的颜色。RGBA
S_COLOR_STROKE = (0, 0, 0, 96)  # 描边颜色。RGBA
# endregion

# MAPS
M_VK2MODIFIER: dict[int, str] = {
    0x11: "ctrl",
    0xA2: "ctrl",
    0xA3: "ctrl",
    0x10: "shift",
    0xA0: "shift",
    0xA1: "shift",
    0x12: "alt",
    0xA4: "alt",
    0xA5: "alt",
    0x5B: "windows",
    0x5C: "windows",
}

M_VK2LOGICNAME: dict[int, str] = {
    0x08: "backspace",
    0x09: "tab",
    0x0D: "enter",
    0x13: "pause",
    0x14: "caps lock",
    0x1B: "esc",
    0x20: "space",
    0x21: "page up",
    0x22: "page down",
    0x23: "end",
    0x24: "home",
    0x25: "left",
    0x26: "up",
    0x27: "right",
    0x28: "down",
    0x2C: "print screen",
    0x2D: "insert",
    0x2E: "delete",
    **{0x30 + i: str(i) for i in range(10)},
    **{0x41 + i: chr(97 + i) for i in range(26)},
    0x5B: "windows",
    0x5C: "windows",
    0x5D: "menu",
    **{0x60 + i: f"numpad {i}" for i in range(10)},
    0x6A: "numpad multiply",
    0x6B: "numpad add",
    0x6D: "numpad subtract",
    0x6E: "numpad decimal",
    0x6F: "numpad divide",
    **{0x70 + i: f"f{i+1}" for i in range(24)},
    0x90: "num lock",
    0x91: "scroll lock",
    **M_VK2MODIFIER,
    0xAD: "volume mute",
    0xAE: "volume down",
    0xAF: "volume up",
    0xB0: "media next track",
    0xB1: "media previous track",
    0xB2: "media stop",
    0xB3: "media play pause",
    0xBA: ";",
    0xBB: "=",
    0xBC: ",",
    0xBD: "-",
    0xBE: ".",
    0xBF: "/",
    0xC0: "`",
    0xDB: "[",
    0xDC: "\\",
    0xDD: "]",
    0xDE: "'",
    0xE2: "non-us backslash",
}

M_VK2SHIFT: dict[int, str] = {
    0x30: ")",
    0x31: "!",
    0x32: "@",
    0x33: "#",
    0x34: "$",
    0x35: "%",
    0x36: "^",
    0x37: "&",
    0x38: "*",
    0x39: "(",
    0xBD: "_",
    0xBB: "+",
    0xDB: "{",
    0xDD: "}",
    0xBA: ":",
    0xDE: '"',
    0xC0: "~",
    0xDC: "|",
    0xBC: "<",
    0xBE: ">",
    0xBF: "?",
}

M_NAME2SYMBOL: dict[str, str] = {
    "space": "␣",
    "enter": "⏎",
    "tab": "⇥",
    "menu": "≡",
    "esc": "⎋",
    "ctrl": "⌃",
    "shift": "⇧",
    "alt": "⎇",  # 2387，也可用Apple式的2325⌥
    "windows": "⊞",
    "num lock": "⇭",
    "caps lock": "⇪",
    "scroll lock": "⤓",
    "insert": "⎀",
    "pause": "⏸",
    "delete": "⌦",
    "backspace": "⌫",
    "home": "⇞",
    "end": "⇟",
    "page up": "⎗",
    "page down": "⎘",
    "up": "↑",
    "down": "↓",
    "left": "←",
    "right": "→",
    "print screen": "⎙",
    "numpad multiply": "×",
    "numpad divide": "÷",
    "numpad add": "+",
    "numpad subtract": "−",
    "numpad enter": "⏎",
    "numpad decimal": ".",
    **{f"numpad {i}": "₀₁₂₃₄₅₆₇₈₉"[i] for i in range(10)},
    **{f"f{i+1}": "①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳㉑㉒㉓㉔"[i] for i in range(24)},
    "volume mute": "🔇",
    "volume down": "🔉",
    "volume up": "🔊",
    "media next track": "⏭",
    "media previous track": "⏮",
    "media stop": "⏹",
    "media play pause": "⏯",
}


def _INITFUNC_jitter_gen():
    def __jitter_gen():
        positions: set[tuple[int, int]] = set(product((-2, 0, 2), (-2, 0, 2)))
        positions -= {(0, 0)}  # 避免最后一次抖动与重置抖动后的位置无法区分
        n = (114, 514)
        while True:
            n = random.choice(list(positions - {n}))
            yield n

    _jg = __jitter_gen()
    jitter_sequence = list(islice(_jg, 1024))
    while True:
        yield from jitter_sequence


@lru_cache(maxsize=384)
def text_get_display(vk: int, modifiers: tuple[int, ...]) -> str:
    shift_pressed = modifiers[1] > 0
    if shift_pressed and vk in M_VK2SHIFT:
        return M_VK2SHIFT[vk]
    name = M_VK2LOGICNAME.get(vk, f"[{vk:02X}]")
    if shift_pressed and len(name) == 1 and name.isalpha():
        return name.upper()
    return M_NAME2SYMBOL.get(name, name)


@lru_cache(maxsize=256)
def text_get_width(text: str, size: int = S_FONT_SIZE) -> int:
    for font in S_FONT_FAMILY:
        try:
            label = Label(text, font_name=font, font_size=size)
            w = label.content_width
            label.delete()
            return w
        except Exception:
            continue
    return 0


@lru_cache(maxsize=256)
def text_get_font(text: str) -> str:
    for font in S_FONT_FAMILY:
        try:
            label = Label(text, font_name=font)
            label.delete()
            return font
        except Exception:
            continue
    return "Last Resort"


V_Gui_update_queue: Queue[tuple[int, E, Any, int]] = Queue()
V_Gui_batch: Batch = Batch()
V_All_rows: list[KeyRow] = []
V_row_lock = threading.Lock()
V_Current_row: KeyRow | None = None
V_Modifier_levels: dict[str, int] = {"ctrl": 0, "shift": 0, "alt": 0, "windows": 0}
V_dirty: int = 3  # 不使用布尔值是因为动画结束后可能没有完整blit上屏
V_timers_jitter: dict[tuple[int, int], _Timer] = {}  # (row_id, key_index) -> _Timer
V_timers_archive: dict[int, _Timer] = {}  # row_id -> _Timer
V_timers_slideout: dict[int, _Timer] = {}  # row_id -> _Timer


_DYNCONST_SPI_GETKEYBOARDDELAY = 0x0016
_DYNCONST_SPI_GETKEYBOARDSPEED = 0x000A
_DYNCONST_SystemParametersInfoW = ctypes.windll.user32.SystemParametersInfoW
_DYNCONST_SystemParametersInfoW.restype = ctypes.c_int
_DYNCONST_SystemParametersInfoW.argtypes = [ctypes.c_uint, ctypes.c_uint, ctypes.c_void_p, ctypes.c_uint]
_DYNCONST_skr_delay_raw = ctypes.c_uint(0)
_DYNCONST_skr_speed_raw = ctypes.c_uint(0)
_DYNCONST_SystemParametersInfoW(_DYNCONST_SPI_GETKEYBOARDDELAY, 0, ctypes.byref(_DYNCONST_skr_delay_raw), 0)
_DYNCONST_SystemParametersInfoW(_DYNCONST_SPI_GETKEYBOARDSPEED, 0, ctypes.byref(_DYNCONST_skr_speed_raw), 0)
_DYNCONST_skr_repeat_rate = 2.5 + _DYNCONST_skr_speed_raw.value * (27.5 / 31.0)  # Hz

C_SCREEN = pyglet.display.get_display().get_default_screen()
C_JITTER_DELAY = (_DYNCONST_skr_delay_raw.value + 1) * 0.25  # s
C_JITTER_INTERVAL = 1.0 / _DYNCONST_skr_repeat_rate if _DYNCONST_skr_repeat_rate > 0 else 0.04  # s
C_MODIFIER_ORDER = list(V_Modifier_levels.keys())
C_COMBO_WIDTH = text_get_width(f"({S_MIN_COMBO})", math.ceil(S_FONT_SIZE * S_COMBO_FONT_SIZE_SCALE))
C_COMBO_FONT = text_get_font("(0123456789)")


S_MARGIN_D = S_MARGIN_D if S_MARGIN_D > 0 else (C_SCREEN.height + S_MARGIN_D)
S_UNDERLINE_MARGIN_U = -S_UNDERLINE_MARGIN_U
S_UNDERLINE_SPACING = -S_UNDERLINE_SPACING


class E(Enum):
    NEW = 1
    UPDATE_COMBO = 2
    RELEASE = 3
    RESET_JITTER = 4
    SCHEDULE_JITTER = 5
    CANCEL_JITTER = 6
    SCHEDULE_ARCHIVE = 7
    CANCEL_ARCHIVE = 8


F_jitter_gen = _INITFUNC_jitter_gen()


class _Timer:
    __slots__ = ("_func",)

    def __init__(self) -> None:
        self._func: Callable[[], None] | None = None

    def _fire(self, _) -> None:
        func = self._func
        self._func = None
        if func is not None:
            func()

    def schedule(self, delay: float, func: Callable[[], None]) -> None:
        self.cancel()
        self._func = func
        pyglet.clock.schedule_once(self._fire, delay)

    def cancel(self) -> None:
        if self._func is not None:
            pyglet.clock.unschedule(self._fire)
            self._func = None

    @property
    def active(self) -> bool:
        return self._func is not None


class KeySprites:
    def __init__(self, base: Label):
        self.base: Label = base
        self.subscript: Label | None = None
        self.attachments: list[Line] = []
        self.base_strokes: list[Label] = []
        self.subscript_strokes: list[Label] = []
        self.attachment_strokes: list[Line] = []
        self._total_width = base.content_width
        self._jitter_x = 0
        self._jitter_y = 0
        self._base_x = 0
        self._base_y = 0
        self._attachment_y_offsets: list[int] = []
        self._attachment_is_new: list[bool] = []
        self._is_modifier: bool = False

        base_text = base.text
        base_font = cast(str, base.font_name)
        base_size = base.font_size
        base_color = base.color
        base_batch = base.batch
        base_x = base.x
        base_y = base.y
        base.delete()

        for dx in [-1, 0, 1]:
            for dy in [-1, 0, 1]:
                if dx == 0 and dy == 0:
                    continue
                stroke = Label(
                    text=base_text,
                    font_name=base_font,
                    font_size=base_size,
                    x=base_x + dx,
                    y=base_y + dy,
                    anchor_x="left",
                    anchor_y="baseline",
                    color=S_COLOR_STROKE,
                    batch=base_batch,
                )
                self.base_strokes.append(stroke)

        self.base = Label(
            text=base_text,
            font_name=base_font,
            font_size=base_size,
            x=base_x,
            y=base_y,
            anchor_x="left",
            anchor_y="baseline",
            color=base_color,
            batch=base_batch,
        )

    def _create_subscript_strokes(self):
        for s in self.subscript_strokes:
            s.delete()
        self.subscript_strokes.clear()
        if not self.subscript:
            return
        sub_text = self.subscript.text
        sub_font = cast(str, self.subscript.font_name)
        sub_size = self.subscript.font_size
        sub_color = self.subscript.color
        sub_batch = self.subscript.batch
        sub_x = self.subscript.x
        sub_y = self.subscript.y
        self.subscript.delete()
        for dx in [-1, 0, 1]:
            for dy in [-1, 0, 1]:
                if dx == 0 and dy == 0:
                    continue
                stroke = Label(
                    text=sub_text,
                    font_name=sub_font,
                    font_size=sub_size,
                    x=sub_x + dx,
                    y=sub_y + dy,
                    anchor_x="left",
                    anchor_y="baseline",
                    color=S_COLOR_STROKE,
                    batch=sub_batch,
                )
                self.subscript_strokes.append(stroke)
        self.subscript = Label(
            text=sub_text,
            font_name=sub_font,
            font_size=sub_size,
            x=sub_x,
            y=sub_y,
            anchor_x="left",
            anchor_y="baseline",
            color=sub_color,
            batch=sub_batch,
        )

    def set_base(self, new_base: Label):
        old_x, old_y = self.base.x, self.base.y
        self.base.delete()
        for s in self.base_strokes:
            s.delete()
        self.base_strokes.clear()
        base_text = new_base.text
        base_font = cast(str, new_base.font_name)
        base_size = new_base.font_size
        base_color = new_base.color
        base_batch = new_base.batch
        new_base.delete()
        for dx in [-1, 0, 1]:
            for dy in [-1, 0, 1]:
                if dx == 0 and dy == 0:
                    continue
                stroke = Label(
                    text=base_text,
                    font_name=base_font,
                    font_size=base_size,
                    x=old_x + dx,
                    y=old_y + dy,
                    anchor_x="left",
                    anchor_y="baseline",
                    color=S_COLOR_STROKE,
                    batch=base_batch,
                )
                self.base_strokes.append(stroke)
        self.base = Label(
            text=base_text,
            font_name=base_font,
            font_size=base_size,
            x=old_x,
            y=old_y,
            anchor_x="left",
            anchor_y="baseline",
            color=base_color,
            batch=base_batch,
        )
        self._total_width = self.base.content_width
        if self.subscript:
            self._total_width += self.subscript.content_width

    def set_subscript(self, label: Label | None):
        if self.subscript:
            self.subscript.delete()
        for s in self.subscript_strokes:
            s.delete()
        self.subscript_strokes.clear()
        self.subscript = label
        self._total_width = self.base.content_width
        if self.subscript:
            self._total_width += self.subscript.content_width
        self._create_subscript_strokes()

    def set_attachments(self, modifiers: tuple[int, ...], is_modifier: bool = False, mod_name: str | None = None):
        self._is_modifier = is_modifier
        for att in self.attachments:
            att.delete()
        self.attachments.clear()
        for s in self.attachment_strokes:
            s.delete()
        self.attachment_strokes.clear()
        self._attachment_y_offsets.clear()
        self._attachment_is_new.clear()

        for i, level in enumerate(modifiers):
            if level > 0:
                j = level - 1
                y_off = S_UNDERLINE_MARGIN_U + j * S_UNDERLINE_SPACING
                self._attachment_y_offsets.append(y_off)
                self._attachment_is_new.append(is_modifier and C_MODIFIER_ORDER[i] == mod_name)
                stroke = Line(0, 0, 0, 0, thickness=4, color=S_COLOR_STROKE, batch=self.base.batch)
                self.attachment_strokes.append(stroke)
                line = Line(0, 0, 0, 0, thickness=2, color=self.base.color, batch=self.base.batch)
                self.attachments.append(line)

    def move_to(self, x: int, y: int):
        self._base_x = x
        self._base_y = y
        actual_x = x + self._jitter_x
        actual_y = y + self._jitter_y
        stroke_dirs = [(dx, dy) for dx in [-1, 0, 1] for dy in [-1, 0, 1] if dx != 0 or dy != 0]
        for i, (dx, dy) in enumerate(stroke_dirs):
            self.base_strokes[i].x = actual_x + dx
            self.base_strokes[i].y = actual_y + dy
        self.base.x = actual_x
        self.base.y = actual_y
        if self.subscript:
            sub_x = actual_x + self.base.content_width
            sub_y = actual_y
            for i, (dx, dy) in enumerate(stroke_dirs):
                self.subscript_strokes[i].x = sub_x + dx
                self.subscript_strokes[i].y = sub_y + dy
            self.subscript.x = sub_x
            self.subscript.y = sub_y
        for line, stroke, y_off, is_new in zip(
            self.attachments,
            self.attachment_strokes,
            self._attachment_y_offsets,
            self._attachment_is_new,
        ):
            line_x = actual_x + S_UNDERLINE_MARGIN_L if is_new else actual_x
            line_y = actual_y + y_off
            line_x2 = actual_x + self._total_width
            stroke.x = line_x
            stroke.y = line_y
            stroke.x2 = line_x2
            stroke.y2 = line_y
            line.x = line_x
            line.y = line_y
            line.x2 = line_x2
            line.y2 = line_y

    def set_jitter(self, dx: int, dy: int):
        self._jitter_x = dx
        self._jitter_y = dy

    def set_color(self, color: tuple[int, int, int, int]):
        self.base.color = color
        for att in self.attachments:
            att.color = color
        if self.subscript:
            self.subscript.color = color

    def delete(self):
        self.base.delete()
        for s in self.base_strokes:
            s.delete()
        if self.subscript:
            self.subscript.delete()
        for s in self.subscript_strokes:
            s.delete()
        for att in self.attachments:
            att.delete()
        for s in self.attachment_strokes:
            s.delete()


class SolidKeyRow:
    def __init__(self, sprites: list[KeySprites]):
        self.sprites = sprites
        self.offsets = [s._base_x for s in sprites] if sprites else []
        self.total_width = sum(s._total_width for s in sprites) if sprites else 0
        if self.offsets:
            base_x = self.offsets[0]
            self.offsets = [x - base_x for x in self.offsets]

    def move_to(self, x: int, y: int):
        for sprite, offset in zip(self.sprites, self.offsets):
            sprite.move_to(x + offset, y)

    def set_color(self, color: tuple[int, int, int, int]):
        for s in self.sprites:
            s.set_color(color)

    def delete(self):
        for s in self.sprites:
            s.delete()


@dataclass(slots=True)
class Key:
    vk: int
    pressed: bool = False
    combo: int = 1
    modifiers: tuple[int, ...] = (0, 0, 0, 0)


@dataclass
class KeyRow:
    keys: list[Key] = field(default_factory=list)
    sprites: list[KeySprites | None] = field(default_factory=list)
    archived: bool = False
    solid_group: SolidKeyRow | None = None
    target_y_offset: float = 0.0
    current_y_offset: float = 0.0
    slideout: bool = False

    def is_idle(self) -> bool:
        return not any(k.pressed for k in reversed(self.keys))

    def solidify(self):
        if (self.solid_group is None) and all(s is not None for s in self.sprites):
            self.solid_group = SolidKeyRow([s for s in self.sprites if s])

    def animate(self, dt: float) -> bool:
        global V_dirty
        diff = self.target_y_offset - self.current_y_offset
        if abs(diff) > 0.1:
            self.current_y_offset += diff * min(1.0, dt * 8)
            V_dirty = 3
        current_y_pos = S_MARGIN_D + self.current_y_offset
        return (current_y_pos < -S_LINE_HEIGHT) or (current_y_pos > C_SCREEN.height + S_LINE_HEIGHT)


def mods_equivalent(vk: int, mods_a: tuple[int, ...], mods_b: tuple[int, ...]) -> bool:
    mod_name = M_VK2MODIFIER.get(vk)
    if mod_name is not None:
        idx = C_MODIFIER_ORDER.index(mod_name)
        return mods_a[:idx] + mods_a[idx + 1 :] == mods_b[:idx] + mods_b[idx + 1 :]
    return mods_a == mods_b


def timers_row_cancel(row: KeyRow) -> None:
    row_id = id(row)
    if timer := V_timers_archive.pop(row_id, None):
        timer.cancel()
    if timer := V_timers_slideout.pop(row_id, None):
        timer.cancel()
    for i in range(len(row.keys)):
        key = (row_id, i)
        if timer := V_timers_jitter.pop(key, None):
            timer.cancel()


def _on_jitter_fire(key: tuple[int, int]) -> None:
    global V_dirty
    row_id, key_index = key
    with V_row_lock:
        target_row = next((r for r in V_All_rows if id(r) == row_id), None)
        if target_row is None or key_index >= len(target_row.keys):
            V_timers_jitter.pop(key, None)
            return
        k = target_row.keys[key_index]
        if not k.pressed:
            V_timers_jitter.pop(key, None)
            return
        if key_index < len(target_row.sprites) and (group := target_row.sprites[key_index]):
            group.set_jitter(*next(F_jitter_gen))
        timer = V_timers_jitter.get(key)
        if timer is not None:
            timer.schedule(C_JITTER_INTERVAL, lambda k=key: _on_jitter_fire(k))
        V_dirty = 3


def _on_archive_fire(row_id: int) -> None:
    global V_dirty
    with V_row_lock:
        target_row = next((r for r in V_All_rows if id(r) == row_id), None)
        if target_row is None or target_row.archived or not target_row.is_idle():
            V_timers_archive.pop(row_id, None)
            return
        target_row.archived = True
        target_row.solidify()
        timer = V_timers_slideout.get(row_id)
        if timer is None:
            timer = _Timer()
            V_timers_slideout[row_id] = timer
        timer.schedule(S_HISTORY_TTL, lambda rid=row_id: _on_slideout_fire(rid))
        V_timers_archive.pop(row_id, None)
        V_dirty = 3


def _on_slideout_fire(row_id: int) -> None:
    global V_dirty
    with V_row_lock:
        target_row = next((r for r in V_All_rows if id(r) == row_id), None)
        if target_row is None:
            V_timers_slideout.pop(row_id, None)
            return
        target_row.slideout = True
        target_row.target_y_offset = ((C_SCREEN.height + S_LINE_HEIGHT * 2) if S_HISTORY_GO_UPWARDS else (-S_LINE_HEIGHT * 2)) - S_MARGIN_D
        V_timers_slideout.pop(row_id, None)
        V_dirty = 3


def _on_key_press(vk: int):
    try:
        with V_row_lock:
            _set_modifier(vk)
            _proc_key_press(vk)
    except Exception:
        traceback.print_exc()


def _set_modifier(vk: int):
    global V_Current_row
    mod_name = M_VK2MODIFIER.get(vk)
    if mod_name and V_Modifier_levels[mod_name] == 0:
        used: set[int] = {v for v in V_Modifier_levels.values() if v > 0}
        if V_Current_row and V_Current_row.keys and used:
            last_used = {v for v in V_Current_row.keys[-1].modifiers if v > 0}
            if len(last_used) > 1:
                used |= last_used
        level = 1
        while level in used:
            level += 1
        V_Modifier_levels[mod_name] = level


def _proc_key_press(vk: int):
    global V_Current_row
    if V_Current_row is None or (V_Current_row.archived and V_Current_row.keys):
        V_Current_row = KeyRow(keys=[], sprites=[])
        V_All_rows.append(V_Current_row)
        while len(V_All_rows) > S_MAX_HISTORY_LINES:
            r = V_All_rows.pop(0)
            timers_row_cancel(r)
            if r.solid_group:
                r.solid_group.delete()
            else:
                for s in r.sprites:
                    if s:
                        s.delete()
    else:
        V_Gui_update_queue.put((-1, E.CANCEL_ARCHIVE, None, id(V_Current_row)))
    if any(V_Current_row.keys[i].vk == vk and V_Current_row.keys[i].pressed for i in range(len(V_Current_row.keys) - 1, -1, -1)):
        return

    current_mods = tuple(V_Modifier_levels.values())
    if V_Current_row.keys and V_Current_row.keys[-1].vk == vk and mods_equivalent(vk, V_Current_row.keys[-1].modifiers, current_mods):
        V_Current_row.keys[-1].combo += 1
        V_Current_row.keys[-1].pressed = True
        V_Gui_update_queue.put((-1, E.UPDATE_COMBO, V_Current_row.keys[-1].combo, id(V_Current_row)))
        V_Gui_update_queue.put((-1, E.SCHEDULE_JITTER, None, id(V_Current_row)))
    else:
        V_Current_row.keys.append(Key(vk, True, 1, current_mods))
        V_Current_row.sprites.append(None)
        idx = len(V_Current_row.keys) - 1
        V_Gui_update_queue.put(
            (
                idx,
                E.NEW,
                (vk, current_mods, S_COLOR_PRESSING),
                id(V_Current_row),
            )
        )
        V_Gui_update_queue.put((idx, E.SCHEDULE_JITTER, None, id(V_Current_row)))


def _on_key_release(vk: int):
    with V_row_lock:
        if not V_Current_row:
            return

        for i in range(len(V_Current_row.keys) - 1, -1, -1):
            if V_Current_row.keys[i].vk != vk or (not V_Current_row.keys[i].pressed):
                continue

            V_Current_row.keys[i].pressed = False
            V_Gui_update_queue.put((i, E.RELEASE, None, id(V_Current_row)))
            V_Gui_update_queue.put((i, E.RESET_JITTER, None, id(V_Current_row)))
            V_Gui_update_queue.put((i, E.CANCEL_JITTER, None, id(V_Current_row)))
            if V_Current_row.is_idle():
                V_Gui_update_queue.put((-1, E.SCHEDULE_ARCHIVE, None, id(V_Current_row)))
            break

        if mod_name := M_VK2MODIFIER.get(vk):
            V_Modifier_levels[mod_name] = 0


def gui_update():
    global V_dirty
    with V_row_lock:
        while True:
            try:
                index, cmd, param, row_id = V_Gui_update_queue.get_nowait()
            except Exception:
                break

            target_row = next((r for r in V_All_rows if id(r) == row_id), None)
            if not target_row or target_row.archived:
                continue

            if index < 0:
                index = len(target_row.sprites) + index

            match cmd:
                case E.NEW:
                    vk, mods, color = cast(tuple[int, tuple[int, ...], tuple[int, int, int, int]], param)
                    render_name = text_get_display(vk, mods)
                    base = Label(
                        text=render_name,
                        font_name=text_get_font(render_name),
                        font_size=S_FONT_SIZE,
                        x=0,
                        y=0,
                        anchor_x="left",
                        anchor_y="baseline",
                        color=color,
                        batch=V_Gui_batch,
                    )
                    sprite = KeySprites(base)
                    is_modifier = vk in M_VK2MODIFIER
                    mod_name = M_VK2MODIFIER.get(vk)
                    sprite.set_attachments(mods, is_modifier, mod_name)
                    target_row.sprites[index] = sprite
                    V_dirty = 3

                case E.UPDATE_COMBO:
                    combo = param
                    sprite = target_row.sprites[index]
                    if not sprite:
                        continue
                    key = target_row.keys[index]
                    base_text = text_get_display(key.vk, key.modifiers)
                    current_color = S_COLOR_PRESSING if key.pressed else S_COLOR_NORMAL
                    use_subscript = (combo >= S_MIN_COMBO) and text_get_width(base_text * combo) > C_COMBO_WIDTH
                    if use_subscript:
                        new_base = Label(
                            text=base_text,
                            font_name=text_get_font(base_text),
                            font_size=S_FONT_SIZE,
                            x=0,
                            y=0,
                            anchor_x="left",
                            anchor_y="baseline",
                            color=current_color,
                            batch=V_Gui_batch,
                        )
                        sprite.set_base(new_base)
                        sub_label = Label(
                            text=f"({combo})",
                            font_name=C_COMBO_FONT,
                            font_size=int(S_FONT_SIZE * S_COMBO_FONT_SIZE_SCALE),
                            x=0,
                            y=0,
                            anchor_x="left",
                            anchor_y="baseline",
                            color=current_color,
                            batch=V_Gui_batch,
                        )
                        sprite.set_subscript(sub_label)
                    else:
                        new_base = Label(
                            text=base_text * combo,
                            font_name=text_get_font(base_text),
                            font_size=S_FONT_SIZE,
                            x=0,
                            y=0,
                            anchor_x="left",
                            anchor_y="baseline",
                            color=current_color,
                            batch=V_Gui_batch,
                        )
                        sprite.set_base(new_base)
                        sprite.set_subscript(None)
                    sprite.set_color(current_color)
                    V_dirty = 3

                case E.RELEASE:
                    if sp := target_row.sprites[index]:
                        sp.set_color(S_COLOR_NORMAL)
                    V_dirty = 3

                case E.RESET_JITTER:
                    if sp := target_row.sprites[index]:
                        sp.set_jitter(0, 0)
                    V_dirty = 3

                case E.SCHEDULE_JITTER:
                    if 0 <= index < len(target_row.keys):
                        key = (row_id, index)
                        timer = V_timers_jitter.get(key)
                        if timer is None:
                            timer = _Timer()
                            V_timers_jitter[key] = timer
                        timer.schedule(C_JITTER_DELAY, lambda k=key: _on_jitter_fire(k))
                        V_dirty = 3

                case E.CANCEL_JITTER:
                    key = (row_id, index)
                    if timer := V_timers_jitter.pop(key, None):
                        timer.cancel()

                case E.SCHEDULE_ARCHIVE:
                    if target_row.is_idle():
                        timer = V_timers_archive.get(row_id)
                        if timer is None:
                            timer = _Timer()
                            V_timers_archive[row_id] = timer
                        timer.schedule(S_LINE_ACTIVE_TIME, lambda rid=row_id: _on_archive_fire(rid))

                case E.CANCEL_ARCHIVE:
                    if timer := V_timers_archive.pop(row_id, None):
                        timer.cancel()

        for mod_name, level in V_Modifier_levels.items():
            if level <= 0:
                continue
            still_pressed = any(k.pressed and M_VK2MODIFIER.get(k.vk) == mod_name for r in V_All_rows if not r.archived for k in r.keys)
            if not still_pressed:
                V_Modifier_levels[mod_name] = 0

        rows_to_remove: list[int] = []
        active_idx = len(V_All_rows) - 1
        for idx, r in enumerate(V_All_rows):
            if not r.archived:
                active_idx = idx
                break

        for i, row in enumerate(V_All_rows):
            if row.archived:
                if not row.slideout and (distance := active_idx - i) > 0:
                    row.target_y_offset = distance * S_LINE_HEIGHT * (1 if S_HISTORY_GO_UPWARDS else -1)
                if row.animate(1 / 60):
                    rows_to_remove.append(i)
            else:
                row.target_y_offset = 0.0
                row.current_y_offset = 0.0

        for i in reversed(rows_to_remove):
            r = V_All_rows.pop(i)
            timers_row_cancel(r)
            if r.solid_group:
                r.solid_group.delete()
            else:
                for s in r.sprites:
                    if s:
                        s.delete()

        for row in V_All_rows:
            y = S_MARGIN_D + int(row.current_y_offset)
            if row.solid_group:
                row.solid_group.move_to(C_SCREEN.width - S_MARGIN_R - row.solid_group.total_width, y)
            else:
                acc_widths = list(accumulate(sprite._total_width for sprite in reversed(row.sprites) if sprite))
                r_baseline = C_SCREEN.width - S_MARGIN_R
                for w, sprite in zip(
                    acc_widths,
                    (s for s in reversed(row.sprites) if s),
                ):
                    sprite.move_to(r_baseline - w, y)

        V_Gui_batch.draw()
        V_dirty -= 1


WS_EX_NOACTIVATE = 0x08000000
WS_EX_TOPMOST = 0x00000008
GWL_EXSTYLE = -20

window = pyglet.window.Window(
    width=C_SCREEN.width,
    height=C_SCREEN.height,
    caption="KeyMon",
    resizable=False,
    style=pyglet.window.Window.WINDOW_STYLE_OVERLAY,
    visible=False,
)

glClearColor(0, 0, 0, 0)
window.clear()

hwnd = ctypes.windll.user32.FindWindowW(None, "KeyMon")
if hwnd:
    prev = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
    ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE, prev | WS_EX_NOACTIVATE | WS_EX_TOPMOST)
    if taskbar := ctypes.windll.user32.FindWindowW("Shell_TrayWnd", None):
        ctypes.windll.user32.SetForegroundWindow(taskbar)

window.set_visible(True)


@window.event
def on_draw():
    global V_dirty
    if not V_dirty and V_Gui_update_queue.empty():
        return
    window.clear()
    gui_update()


def cleanup():
    pyllkb.set_press_callback(None)
    pyllkb.set_release_callback(None)
    pyllkb.stop()
    for timer in V_timers_jitter.values():
        timer.cancel()
    V_timers_jitter.clear()
    for timer in V_timers_archive.values():
        timer.cancel()
    V_timers_archive.clear()
    for timer in V_timers_slideout.values():
        timer.cancel()
    V_timers_slideout.clear()
    with V_row_lock:
        for row in V_All_rows:
            if row.solid_group:
                row.solid_group.delete()
            else:
                for s in row.sprites:
                    if s:
                        s.delete()
    if window:
        window.close()


def main():
    atexit.register(cleanup)
    pyllkb.set_press_callback(_on_key_press)
    pyllkb.set_release_callback(_on_key_release)
    pyllkb.start()
    pyglet.app.run(interval=1 / 60)


if __name__ == "__main__":
    main()
