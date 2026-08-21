#!/usr/bin/env python3
"""
共读小屋 —— 和你的AI一起读书的网页
纯标准库实现，无第三方依赖。

功能一：纯阅读模式（翻页阅读器 + 进度记忆，讨论走TG）
功能二：批注共读模式（划线/写想法=粉色气泡，Rhys回应=蓝色气泡）

数据结构：
  /root/reading/books/<slug>/
      meta.json          {title, chapters:[...], created}
      chapters/NNN.txt   单章正文
      annotations/NNN.json  [{id, anchor, note, who, ts, replies:[{who,text,ts}]}]
  /root/reading/progress.json  {slug: {ch, page, mode, ts}}
"""
import json
import os
import re
import shutil
import threading
import time
import urllib.request
import uuid
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import unquote, urlparse

ROOT = os.path.dirname(os.path.abspath(__file__))
# Railway 分支改动：托管平台上 /app 每次部署都是全新的，数据必须落在挂载的卷上；
# 密码和 key 不该写进仓库；端口由平台指定。所以这几项都改成「环境变量优先，
# 没有就回退原来的行为」——本地 python3 app.py 完全照旧，一点没变。
DATA_DIR = os.environ.get("DATA_DIR") or ROOT
BOOKS_DIR = os.environ.get("BOOKS_DIR") or os.path.join(DATA_DIR, "books")
PROGRESS_FILE = os.path.join(DATA_DIR, "progress.json")

# 所有个人化配置都在 config.json（见 config.example.json）
try:
    with open(os.path.join(ROOT, "config.json"), encoding="utf-8") as _f:
        CFG = json.load(_f)
except (OSError, json.JSONDecodeError):
    CFG = {}
PASSCODE = str(os.environ.get("PASSCODE") or CFG.get("passcode", "0000"))
PORT = int(os.environ.get("PORT") or CFG.get("port", 8000))
SUBTITLE = CFG.get("subtitle", "two readers, one book")
LOGIN_HINT = CFG.get("login_hint", "四位数密码")
USER_NAME = CFG.get("user_name", "我")
AI_NAME = CFG.get("ai_name", "AI")
GARDENER_LOG = CFG.get("gardener_log", "")

os.makedirs(BOOKS_DIR, exist_ok=True)
os.makedirs(DATA_DIR, exist_ok=True)

# ---------------- 数据层 ----------------

def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError):
        return default


def save_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def list_books():
    books = []
    for slug in sorted(os.listdir(BOOKS_DIR)):
        meta_path = os.path.join(BOOKS_DIR, slug, "meta.json")
        meta = load_json(meta_path, None)
        if meta:
            meta["slug"] = slug
            books.append(meta)
    return books


def decode_text(raw: bytes) -> str:
    for enc in ("utf-8-sig", "utf-16", "gb18030", "big5"):
        try:
            text = raw.decode(enc)
            # utf-16 误判保护：解出来全是乱码时中文占比会极低
            if enc != "utf-8-sig":
                sample = text[:2000]
                cjk = sum(1 for c in sample if "一" <= c <= "鿿")
                if len(sample) > 100 and cjk < 5:
                    continue
            return text
        except (UnicodeDecodeError, UnicodeError):
            continue
    return raw.decode("utf-8", errors="replace")


# 多种常见章节标记，按命中数取最优
CHAPTER_PATTERNS = [
    # 第X章 / 第X回 …，以及 序章/楔子/番外 等
    r"^\s*((?:第\s*[0-9一二三四五六七八九十百千两〇零]+\s*[章节回卷部集])[^\n]{0,40}"
    r"|(?:序章|序幕|楔子|引子|尾声|终章|后记|番外)[^\n]{0,40}"
    r"|(?:Chapter|CHAPTER)\s+\d+[^\n]{0,40})\s*$",
    # 0001 01 标题 / 0087 终章 …（连载编号式）
    r"^\s*(\d{3,4}\s+[^\n]{1,40}?)\s*$",
    # 01 标题 / 1、标题 / 1.标题
    r"^\s*(\d{1,4}\s*[、.．·:：\s][^\n]{1,35}?)\s*$",
    # 一、标题
    r"^\s*([一二三四五六七八九十百]+\s*[、.．·:：][^\n]{1,35}?)\s*$",
]


def _split_by_matches(text, matches):
    chapters = []
    head = text[: matches[0].start()].strip()
    if len(head) > 200:
        chapters.append(("开篇", head))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[m.end(): end].strip()
        title = m.group(1).strip()
        if body:
            chapters.append((title, body))
    return chapters


def _size_split(text):
    paras = [p for p in text.split("\n") if p.strip()]
    chapters, buf, size = [], [], 0
    for p in paras:
        buf.append(p)
        size += len(p)
        if size >= 8000:
            chapters.append((f"第{len(chapters)+1}部分", "\n".join(buf)))
            buf, size = [], 0
    if buf:
        chapters.append((f"第{len(chapters)+1}部分", "\n".join(buf)))
    return chapters


def ai_split(text: str):
    """DeepSeek 辅助拆章：把候选标题行发给API，让它挑出真正的章节标题行号。"""
    cfg = load_json(os.path.join(ROOT, "config.json"), {})
    key = cfg.get("deepseek_api_key", "")
    if not key:
        return None
    lines = text.split("\n")
    cands = [(i, s.strip()) for i, s in enumerate(lines)
             if s.strip() and len(s.strip()) <= 40
             and re.search(r"\d|第.{1,8}[章节回卷]|序章|楔子|尾声|番外|终章", s)]
    if not cands or len(cands) > 2000:
        return None
    listing = "\n".join(f"{i}|{s}" for i, s in cands)
    prompt = (
        "下面是一本小说里可能是章节标题的行，格式为 行号|内容。"
        "请判断哪些行是真正的章节标题（成体系、编号连续的那种），"
        "只返回JSON，格式 {\"headings\": [行号, ...]}，不要任何其他文字。\n\n" + listing)
    try:
        content = ds_chat("你是小说章节结构分析助手。", prompt,
                          task="拆章判断", detail=f"{len(cands)}个候选标题行",
                          json_mode=True, max_tokens=2000)
        nums = json.loads(content)["headings"]
        nums = sorted({int(n) for n in nums if 0 <= int(n) < len(lines)})
    except Exception:
        return None
    if len(nums) < 3:
        return None
    chapters = []
    head = "\n".join(lines[: nums[0]]).strip()
    if len(head) > 200:
        chapters.append(("开篇", head))
    for j, n in enumerate(nums):
        end = nums[j + 1] if j + 1 < len(nums) else len(lines)
        body = "\n".join(lines[n + 1: end]).strip()
        if body:
            chapters.append((lines[n].strip(), body))
    return chapters if len(chapters) >= 3 else None


def split_chapters(text: str):
    """返回 [(title, body), ...]。本地多模式优先，DeepSeek兜底，最后按字数切。"""
    best = None
    for pat in CHAPTER_PATTERNS:
        matches = list(re.finditer(pat, text, re.MULTILINE))
        # 模式按精确度排序，靠后的宽松模式要多命中15%以上才能取代
        if len(matches) >= 3 and (best is None or len(matches) > len(best) * 1.15):
            best = matches
    if best:
        chapters = _split_by_matches(text, best)
        # 平均章节太小说明误匹配（比如把对话行当标题），弃用
        if chapters and sum(len(b) for _, b in chapters) / len(chapters) > 500:
            return chapters
    chapters = ai_split(text)
    if chapters:
        return chapters
    return _size_split(text)


# 常见非文本格式的文件头。改后缀不等于转格式——PDF 改名成 .txt 传上来，
# gb18030 几乎能把任何字节都"解码"成乱码汉字，于是从前会静悄悄拆出一本乱码书。
MAGIC = [
    (b"%PDF", "PDF"), (b"PK\x03\x04", "Word/EPUB/zip"),
    (b"\xd0\xcf\x11\xe0", "老版 Word/Excel"), (b"{\\rtf", "RTF"),
    (b"\x89PNG", "PNG 图片"), (b"\xff\xd8\xff", "JPEG 图片"),
    (b"GIF8", "GIF 图片"), (b"\x1f\x8b", "gzip 压缩包"),
]


def _reject_if_binary(raw: bytes, text: str):
    for sig, what in MAGIC:
        if raw.startswith(sig):
            raise ValueError(f"这是{what}，不是纯文本。改后缀变不成 txt，得先转格式。")
    # 兜底：正常中文里几乎不会出现控制字符（制表/换行除外）
    sample = text[:4000]
    if not sample:
        return
    bad = sum(1 for c in sample if (c < " " and c not in "\t\n\r") or c == "\ufffd")
    if bad > len(sample) * 0.02:
        raise ValueError("这不像纯文本文件（里面有大量乱码）。先确认它本身就是 txt。")


def save_book(filename: str, raw: bytes):
    title = re.sub(r"\.(txt|text)$", "", filename, flags=re.I).strip() or "未命名"
    slug = re.sub(r"[^\w一-鿿-]+", "-", title).strip("-") or f"book-{int(time.time())}"
    text = decode_text(raw)
    _reject_if_binary(raw, text)
    chapters = split_chapters(text)
    if not chapters:
        raise ValueError("empty book")
    bdir = os.path.join(BOOKS_DIR, slug)
    os.makedirs(os.path.join(bdir, "chapters"), exist_ok=True)
    os.makedirs(os.path.join(bdir, "annotations"), exist_ok=True)
    for i, (_t, body) in enumerate(chapters):
        with open(os.path.join(bdir, "chapters", f"{i:03d}.txt"), "w", encoding="utf-8") as f:
            f.write(body)
    meta = {
        "title": title,
        "chapters": [t for t, _ in chapters],
        "created": time.strftime("%Y-%m-%d %H:%M"),
    }
    save_json(os.path.join(bdir, "meta.json"), meta)
    return slug, meta


def get_chapter(slug, idx):
    meta = load_json(os.path.join(BOOKS_DIR, slug, "meta.json"), None)
    if not meta or not 0 <= idx < len(meta["chapters"]):
        return None
    path = os.path.join(BOOKS_DIR, slug, "chapters", f"{idx:03d}.txt")
    try:
        with open(path, encoding="utf-8") as f:
            text = f.read()
    except OSError:
        return None
    return {
        "title": meta["chapters"][idx],
        "book": meta["title"],
        "index": idx,
        "total": len(meta["chapters"]),
        "chapters": meta["chapters"],
        "text": text,
    }


def anno_path(slug, idx):
    return os.path.join(BOOKS_DIR, slug, "annotations", f"{idx:03d}.json")


def note_path(slug, idx):
    return os.path.join(BOOKS_DIR, slug, "notes", f"{idx:03d}.md")


DS_LOG = os.path.join(ROOT, "ds_log.json")
_ds_log_lock = threading.Lock()


def ds_log_add(entry):
    with _ds_log_lock:
        log = load_json(DS_LOG, [])
        entry["ts"] = time.strftime("%Y-%m-%d %H:%M")
        log.append(entry)
        save_json(DS_LOG, log[-500:])


def ds_chat(system, user, task="", detail="", json_mode=False, max_tokens=600):
    key = os.environ.get("DEEPSEEK_API_KEY") or load_json(os.path.join(ROOT, "config.json"), {}).get("deepseek_api_key", "")
    if not key:
        return None
    payload = {
        "model": "deepseek-chat",
        "messages": [{"role": "system", "content": system},
                     {"role": "user", "content": user}],
        "temperature": 0.3 if not json_mode else 0,
        "max_tokens": max_tokens,
    }
    if json_mode:
        payload["response_format"] = {"type": "json_object"}
    req = urllib.request.Request(
        "https://api.deepseek.com/chat/completions",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json",
                 "Authorization": f"Bearer {key}"})
    t0 = time.time()
    try:
        with urllib.request.urlopen(req, timeout=120) as r:
            resp = json.load(r)
    except Exception as e:
        ds_log_add({"task": task or "调用", "detail": detail,
                    "ok": False, "error": str(e)[:100]})
        raise
    usage = resp.get("usage", {})
    ds_log_add({"task": task or "调用", "detail": detail, "ok": True,
                "tokens_in": usage.get("prompt_tokens"),
                "tokens_out": usage.get("completion_tokens"),
                "secs": round(time.time() - t0, 1)})
    return resp["choices"][0]["message"]["content"].strip()


NOTE_PROMPT = (
    "你是共读助手，为AI伙伴生成剧情笔记，帮它快速恢复上下文而不必重读全文。"
    "请为这一章写150-250字笔记，包含：出场人物及关系、主要事件、关键伏笔或细节、章末状态。"
    "直接输出笔记正文，不要标题。")


def gen_notes_async(slug):
    """后台线程：用DeepSeek为整本书逐章生成剧情笔记，已有的跳过。"""
    def work():
        meta = load_json(os.path.join(BOOKS_DIR, slug, "meta.json"), None)
        if not meta:
            return
        ndir = os.path.join(BOOKS_DIR, slug, "notes")
        os.makedirs(ndir, exist_ok=True)
        for i in range(len(meta["chapters"])):
            np = note_path(slug, i)
            if os.path.exists(np):
                continue
            ch = get_chapter(slug, i)
            if not ch:
                continue
            try:
                note = ds_chat(NOTE_PROMPT, f"《{meta['title']}》{ch['title']}\n\n{ch['text'][:8000]}",
                               task="剧情笔记", detail=f"{meta['title']}·{ch['title'][:20]}")
            except Exception:
                time.sleep(5)
                continue
            if note:
                with open(np, "w", encoding="utf-8") as f:
                    f.write(f"# {ch['title']}\n\n{note}\n")
            time.sleep(0.5)
    threading.Thread(target=work, daemon=True).start()


# ---------------- 主题 ----------------
# 每个主题 = day全量变量 + night差量覆盖。结构类风格（黏土/新拟物/玻璃）靠
# --radius/--shadow/--cbd/--sblur/--btnsh 等结构变量实现，页面CSS统一消费。
THEMES = {
    "puppy": {"label": "🍪 奶油小狗", "sticker": "🐶",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='170' height='170'><text x='16' y='36' font-size='15' opacity='.5' fill='#c08a4f'>✦</text><text x='108' y='64' font-size='16' opacity='.35'>🐾</text><text x='56' y='120' font-size='12' opacity='.45' fill='#e8a0ac'>♡</text><text x='132' y='152' font-size='11' opacity='.5' fill='#93bce0'>✦</text></svg>",
     "decoN": "<svg xmlns='http://www.w3.org/2000/svg' width='170' height='170'><text x='16' y='36' font-size='15' opacity='.25' fill='#aab8d8'>✦</text><text x='108' y='64' font-size='16' opacity='.15'>🐾</text><text x='56' y='120' font-size='12' opacity='.2' fill='#c8909e'>♡</text><text x='132' y='152' font-size='11' opacity='.22' fill='#93bce0'>✦</text></svg>", "day": {
        "--bg": "#fbf2de", "--card": "#fffdf6", "--ink": "#4a4038", "--sub": "#a5977f",
        "--accent": "#c94f4f", "--pink": "#ffe9ed", "--pink-line": "#f0a8b8",
        "--blue": "#e3f0fb", "--blue-line": "#93bce0", "--mark": "#fdeac2",
        "--pink-ink": "#c25e70", "--blue-ink": "#4a78a8", "--line": "#f0e4cd",
        "--radius": "18px", "--cbd": "1.5px solid #d8e6f4",
        "--shadow": "0 2px 8px rgba(147,188,224,.25)"},
     "night": {
        "--bg": "#20242e", "--card": "#2a2f3b", "--ink": "#e6e1d4", "--sub": "#8b91a0",
        "--accent": "#e08a8a", "--pink": "#3d2f37", "--pink-line": "#b87f92",
        "--blue": "#2a3a4d", "--blue-line": "#7fa8d0", "--mark": "#4a3e26",
        "--pink-ink": "#e3a3b0", "--blue-ink": "#9cc0e8", "--line": "#3a4150",
        "--cbd": "1.5px solid #39445a", "--shadow": "0 2px 10px rgba(0,0,0,.4)"}},
    "matcha": {"label": "🍵 抹茶老铺", "sticker": "🍵",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='180' height='180'><text x='20' y='44' font-size='16' opacity='.3'>🍃</text><text x='120' y='90' font-size='14' opacity='.4' fill='#5a7a4c'>❋</text><text x='60' y='150' font-size='11' opacity='.35' fill='#c9a578'>◦</text><text x='150' y='160' font-size='12' opacity='.35' fill='#5a7a4c'>❋</text></svg>",
     "decoN": "<svg xmlns='http://www.w3.org/2000/svg' width='180' height='180'><text x='20' y='44' font-size='16' opacity='.14'>🍃</text><text x='120' y='90' font-size='14' opacity='.2' fill='#a3c088'>❋</text><text x='150' y='160' font-size='12' opacity='.18' fill='#a3c088'>❋</text></svg>", "day": {
        "--bg": "#e9ecd9", "--card": "#f8f9ec", "--ink": "#333f2b", "--sub": "#87927a",
        "--accent": "#5a7a4c", "--pink": "#f2e8d8", "--pink-line": "#c9a578",
        "--blue": "#e0ead9", "--blue-line": "#87a578", "--mark": "#e3e8c4",
        "--pink-ink": "#96703d", "--blue-ink": "#4c6b3d", "--line": "#dde2c6",
        "--radius": "12px", "--cbd": "1px solid #cdd6b4",
        "--shadow": "0 1px 4px rgba(90,122,76,.15)"},
     "night": {
        "--bg": "#181f15", "--card": "#232c1e", "--ink": "#dde3cd", "--sub": "#8a9680",
        "--accent": "#a3c088", "--pink": "#33301f", "--pink-line": "#a08a58",
        "--blue": "#25301f", "--blue-line": "#7d9a68", "--mark": "#39402a",
        "--pink-ink": "#cdb083", "--blue-ink": "#a8c890", "--line": "#333d2b",
        "--cbd": "1px solid #37432c", "--shadow": "0 1px 6px rgba(0,0,0,.5)"}},
    "mucha": {"label": "🌿 慕夏花神", "sticker": "🌷",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='190' height='190'><text x='18' y='42' font-size='17' opacity='.35' fill='#a8823f'>✿</text><text x='120' y='84' font-size='15' opacity='.4' fill='#7c8449'>❦</text><text x='58' y='146' font-size='13' opacity='.35' fill='#a8823f'>❧</text><text x='150' y='172' font-size='14' opacity='.3' fill='#7c8449'>✿</text></svg>",
     "decoN": "<svg xmlns='http://www.w3.org/2000/svg' width='190' height='190'><text x='18' y='42' font-size='17' opacity='.18' fill='#c8a45c'>✿</text><text x='120' y='84' font-size='15' opacity='.2' fill='#8f9a5c'>❦</text><text x='150' y='172' font-size='14' opacity='.15' fill='#c8a45c'>✿</text></svg>", "day": {
        "--bg": "#f0e9d6", "--card": "#faf5e6", "--ink": "#4b4331", "--sub": "#998c6d",
        "--accent": "#7c8449", "--pink": "#f4e4d0", "--pink-line": "#cf9d6e",
        "--blue": "#e6e8d2", "--blue-line": "#9aa46c", "--mark": "#eadfb4",
        "--pink-ink": "#a06b3a", "--blue-ink": "#6b7440", "--line": "#e0d5b2",
        "--radius": "10px", "--cbd": "1px solid #cbbd8c",
        "--shadow": "0 1px 5px rgba(150,130,80,.18)"},
     "night": {
        "--bg": "#231f14", "--card": "#2e281a", "--ink": "#e5dcc0", "--sub": "#9a8f70",
        "--accent": "#c8a45c", "--pink": "#362b1c", "--pink-line": "#b08a54",
        "--blue": "#2c2e1c", "--blue-line": "#8f9a5c", "--mark": "#403820",
        "--pink-ink": "#d0aa72", "--blue-ink": "#b2bc7a", "--line": "#3d3620",
        "--cbd": "1px solid #4c4226", "--shadow": "0 1px 6px rgba(0,0,0,.5)"}},
    "bwcute": {"label": "🎀 黑白甜", "sticker": "🎀",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='170' height='170'><text x='14' y='38' font-size='14' opacity='.16' fill='#2a2a2a'>★</text><text x='104' y='66' font-size='15' opacity='.3'>🎀</text><text x='52' y='122' font-size='11' opacity='.18' fill='#2a2a2a'>✧</text><text x='134' y='152' font-size='12' opacity='.15' fill='#2a2a2a'>♪</text></svg>",
     "decoN": "<svg xmlns='http://www.w3.org/2000/svg' width='170' height='170'><text x='14' y='38' font-size='14' opacity='.2' fill='#e8e8e8'>★</text><text x='104' y='66' font-size='15' opacity='.18'>🎀</text><text x='52' y='122' font-size='11' opacity='.22' fill='#e8e8e8'>✧</text></svg>", "day": {
        "--bg": "#f5f5f5", "--card": "#ffffff", "--ink": "#262626", "--sub": "#9a9a9a",
        "--accent": "#1a1a1a", "--pink": "#efefef", "--pink-line": "#c8c8c8",
        "--blue": "#e6e6e6", "--blue-line": "#8f8f8f", "--mark": "#e2e2e2",
        "--pink-ink": "#555555", "--blue-ink": "#333333", "--line": "#e8e8e8",
        "--radius": "20px", "--cbd": "1.5px solid #262626",
        "--shadow": "3px 3px 0 rgba(38,38,38,.9)",
        "--font": "-apple-system,'PingFang SC','Microsoft YaHei',sans-serif"},
     "night": {
        "--bg": "#141414", "--card": "#1f1f1f", "--ink": "#ececec", "--sub": "#8a8a8a",
        "--accent": "#f0f0f0", "--pink": "#2c2c2c", "--pink-line": "#6a6a6a",
        "--blue": "#262626", "--blue-line": "#909090", "--mark": "#3a3a3a",
        "--pink-ink": "#c8c8c8", "--blue-ink": "#dcdcdc", "--line": "#333333",
        "--cbd": "1.5px solid #e8e8e8", "--shadow": "3px 3px 0 rgba(232,232,232,.85)"}},
    "bluecard": {"label": "🕊 法式蓝笺", "sticker": "🕊",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='190' height='190'><text x='18' y='44' font-size='15' opacity='.3'>🕊</text><text x='118' y='88' font-size='14' opacity='.35' fill='#5a72b0'>❧</text><text x='58' y='148' font-size='12' opacity='.3' fill='#7e97c8'>✻</text><text x='150' y='170' font-size='11' opacity='.3' fill='#5a72b0'>❦</text></svg>",
     "decoN": "<svg xmlns='http://www.w3.org/2000/svg' width='190' height='190'><text x='18' y='44' font-size='15' opacity='.14'>🕊</text><text x='118' y='88' font-size='14' opacity='.2' fill='#93aade'>❧</text><text x='58' y='148' font-size='12' opacity='.16' fill='#93aade'>✻</text></svg>", "day": {
        "--bg": "#f6f3ea", "--card": "#fdfcf6", "--ink": "#39466b", "--sub": "#8b96b0",
        "--accent": "#5a72b0", "--pink": "#edf1fa", "--pink-line": "#aab9de",
        "--blue": "#e2eaf6", "--blue-line": "#7e97c8", "--mark": "#dce6f5",
        "--pink-ink": "#5a6ea8", "--blue-ink": "#46609e", "--line": "#e3e2d4",
        "--radius": "8px", "--cbd": "1px solid #c3cfe6",
        "--shadow": "0 1px 3px rgba(90,114,176,.15)"},
     "night": {
        "--bg": "#131828", "--card": "#1c2336", "--ink": "#d6deee", "--sub": "#7f8aa8",
        "--accent": "#93aade", "--pink": "#242c44", "--pink-line": "#7688c0",
        "--blue": "#20293e", "--blue-line": "#6f88c0", "--mark": "#2d3a58",
        "--pink-ink": "#a8b8e8", "--blue-ink": "#93aade", "--line": "#2a3350",
        "--cbd": "1px solid #333f60", "--shadow": "0 1px 5px rgba(0,0,0,.5)"}},
    "clay": {"label": "🍡 黏土", "sticker": "🍡",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='200' height='200'><circle cx='34' cy='40' r='14' fill='#e8a0c8' opacity='.22'/><circle cx='140' cy='86' r='10' fill='#b3a2e8' opacity='.25'/><circle cx='70' cy='156' r='8' fill='#f5c990' opacity='.3'/><circle cx='176' cy='170' r='12' fill='#a0d8c8' opacity='.22'/></svg>",
     "decoN": "<svg xmlns='http://www.w3.org/2000/svg' width='200' height='200'><circle cx='34' cy='40' r='14' fill='#e8a0c8' opacity='.1'/><circle cx='140' cy='86' r='10' fill='#b3a2e8' opacity='.12'/><circle cx='176' cy='170' r='12' fill='#a0d8c8' opacity='.1'/></svg>", "day": {
        "--bg": "#efeafa", "--card": "#faf7ff", "--ink": "#4c4460", "--sub": "#a094ba",
        "--accent": "#d4739a", "--pink": "#fce2ee", "--pink-line": "#eba4c8",
        "--blue": "#e5dcfa", "--blue-line": "#b3a2e8", "--mark": "#fdedd4",
        "--pink-ink": "#c05c8a", "--blue-ink": "#7a68b8", "--line": "#eae2f6",
        "--radius": "24px", "--bradius": "18px",
        "--shadow": "0 10px 22px rgba(163,140,210,.28),inset 0 -5px 10px rgba(163,140,210,.16),inset 0 4px 8px rgba(255,255,255,.95)",
        "--btnsh": "0 5px 12px rgba(163,140,210,.35),inset 0 -3px 6px rgba(163,140,210,.25),inset 0 2px 4px rgba(255,255,255,.9)",
        "--btnsh-a": "0 2px 5px rgba(163,140,210,.3),inset 0 3px 6px rgba(163,140,210,.3)",
        "--font": "-apple-system,'PingFang SC','Microsoft YaHei',sans-serif"},
     "night": {
        "--bg": "#252038", "--card": "#312a48", "--ink": "#e8e2f5", "--sub": "#948aae",
        "--accent": "#e895b8", "--pink": "#43304a", "--pink-line": "#c8809f",
        "--blue": "#363050", "--blue-line": "#9a8ad0", "--mark": "#4a3d2b",
        "--pink-ink": "#eba4c0", "--blue-ink": "#b0a2e0", "--line": "#3d3556",
        "--shadow": "0 10px 22px rgba(0,0,0,.45),inset 0 -5px 10px rgba(0,0,0,.3),inset 0 4px 8px rgba(255,255,255,.07)",
        "--btnsh": "0 5px 12px rgba(0,0,0,.4),inset 0 -3px 6px rgba(0,0,0,.3),inset 0 2px 4px rgba(255,255,255,.08)",
        "--btnsh-a": "0 2px 5px rgba(0,0,0,.4),inset 0 3px 6px rgba(0,0,0,.35)"}},
    "neu": {"label": "🌫 新拟物", "day": {
        "--bg": "#e0e5ec", "--card": "#e0e5ec", "--ink": "#44506a", "--sub": "#8e9ab5",
        "--accent": "#5d7290", "--pink": "#e4e0ea", "--pink-line": "#b0a0b8",
        "--blue": "#dde4ef", "--blue-line": "#93a8c8", "--mark": "#cfd8e6",
        "--pink-ink": "#8a7898", "--blue-ink": "#5d7290", "--line": "#cdd4de",
        "--radius": "18px", "--bradius": "14px",
        "--shadow": "9px 9px 18px #bec4cf,-9px -9px 18px #ffffff",
        "--btnsh": "6px 6px 12px #bec4cf,-6px -6px 12px #ffffff",
        "--btnsh-a": "inset 4px 4px 8px #bec4cf,inset -4px -4px 8px #ffffff",
        "--font": "-apple-system,'PingFang SC','Microsoft YaHei',sans-serif"},
     "night": {
        "--bg": "#2b3038", "--card": "#2b3038", "--ink": "#ccd4e0", "--sub": "#7d8797",
        "--accent": "#8fa8c8", "--pink": "#2f3038", "--pink-line": "#8a7890",
        "--blue": "#2b333f", "--blue-line": "#7590b0", "--mark": "#3d4450",
        "--pink-ink": "#b39ec0", "--blue-ink": "#94b0d0", "--line": "#3a414c",
        "--shadow": "8px 8px 16px #23272d,-8px -8px 16px #333a43",
        "--btnsh": "5px 5px 10px #23272d,-5px -5px 10px #333a43",
        "--btnsh-a": "inset 4px 4px 8px #23272d,inset -4px -4px 8px #333a43"}},
    "glass": {"label": "🫧 拟态玻璃", "sticker": "🫧",
     "deco": "<svg xmlns='http://www.w3.org/2000/svg' width='220' height='220'><circle cx='40' cy='50' r='16' fill='none' stroke='#ffffff' stroke-width='1.5' opacity='.5'/><circle cx='150' cy='100' r='9' fill='#ffffff' opacity='.25'/><circle cx='80' cy='170' r='12' fill='none' stroke='#ffffff' stroke-width='1' opacity='.4'/><circle cx='195' cy='190' r='6' fill='#ffffff' opacity='.3'/></svg>", "day": {
        "--bg": "linear-gradient(135deg,#c9d6f5 0%,#e6d3ee 45%,#cde9f2 100%) fixed",
        "--card": "rgba(255,255,255,.5)", "--ink": "#3b4058", "--sub": "#7d84a0",
        "--accent": "#7568cc", "--pink": "rgba(255,214,228,.65)",
        "--pink-line": "rgba(228,130,162,.8)", "--blue": "rgba(205,228,252,.6)",
        "--blue-line": "rgba(120,160,215,.85)", "--mark": "rgba(255,225,160,.75)",
        "--pink-ink": "#b05a80", "--blue-ink": "#4a6aa8", "--line": "rgba(255,255,255,.5)",
        "--radius": "18px", "--cbd": "1px solid rgba(255,255,255,.65)",
        "--sblur": "blur(14px)", "--shadow": "0 8px 28px rgba(100,110,180,.22)"},
     "night": {
        "--bg": "linear-gradient(135deg,#171c34 0%,#2c1e44 50%,#122736 100%) fixed",
        "--card": "rgba(255,255,255,.09)", "--ink": "#e8e9f5", "--sub": "#9298b5",
        "--accent": "#a89cf0", "--pink": "rgba(240,140,180,.18)",
        "--pink-line": "rgba(240,150,185,.55)", "--blue": "rgba(130,180,250,.16)",
        "--blue-line": "rgba(140,180,245,.55)", "--mark": "rgba(255,210,120,.28)",
        "--pink-ink": "#f0a8c5", "--blue-ink": "#a5c5f5", "--line": "rgba(255,255,255,.14)",
        "--cbd": "1px solid rgba(255,255,255,.2)", "--sblur": "blur(14px)",
        "--shadow": "0 8px 28px rgba(0,0,0,.35)"}},
}

# 划线/字色可选色板
PALETTES = {
    "黑白": ["#111111", "#3d3d3d", "#6e6e6e", "#a3a3a3", "#d4d4d4", "#f5f5f5"],
    "莫兰迪": ["#b9a7a0", "#c5b7ac", "#a7b5a4", "#98a8b8", "#c0b2c5", "#d4c0a8"],
    "多巴胺": ["#ff5c8a", "#ff9f43", "#ffd93d", "#1dd1a1", "#54a0ff", "#b980f0"],
    "薄荷曼波": ["#b8f0d8", "#7fe3c3", "#5ec8e5", "#9bd8f0", "#3aa8a0", "#e0fbf0"],
}

# 页面公共结构样式：消费主题的结构变量，追加在页面自身CSS之后以获得覆盖权
EXTRA_CSS = """<style>
body{background:var(--bgfull,var(--bg))}
.card,.item,.stat>div,.info,.sheet{border-radius:var(--radius,16px);
box-shadow:var(--shadow,0 1px 6px rgba(120,90,60,.08));border:var(--cbd,none);
backdrop-filter:var(--sblur,none);-webkit-backdrop-filter:var(--sblur,none)}
.sheet{border-radius:var(--radius,16px) var(--radius,16px) 0 0}
button{transition:transform .15s,box-shadow .15s,filter .2s}
button:active{transform:scale(.96)}
.card{transition:transform .2s,box-shadow .2s;position:relative}
@media(hover:hover){.card:hover{transform:translateY(-2px)}}
.card::after{content:var(--sticker,"");position:absolute;top:-11px;right:14px;
font-size:22px;transform:rotate(10deg);pointer-events:none;
filter:drop-shadow(0 2px 3px rgba(0,0,0,.18))}
.modes button,.srow button{box-shadow:var(--btnsh,none);border-radius:var(--bradius,10px)}
.modes button:active,.srow button:active{box-shadow:var(--btnsh-a,var(--btnsh,none))}
/* 各主题的专属装饰（照搬参考图的视觉语言） */
.th-puppy .card{background-image:repeating-linear-gradient(90deg,rgba(147,188,224,.3) 0 12px,transparent 12px 24px);background-size:100% 7px;background-repeat:no-repeat;background-position:top}
.th-matcha .card{border-left:4px solid var(--accent)}
.th-mucha .card{outline:1px solid rgba(160,135,80,.5);outline-offset:-6px}
.th-bwcute .card{outline:1.5px dashed rgba(130,130,130,.5);outline-offset:-6px}
.th-bluecard .card{outline:1px solid rgba(110,130,180,.4);outline-offset:-5px}
.th-glass #rnfab,.th-glass .up{backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px)}
#rnfab{position:fixed;right:16px;bottom:20px;z-index:40;width:44px;height:44px;
border-radius:50%;background:var(--card);color:var(--ink);font-size:20px;
box-shadow:var(--shadow,0 1px 6px rgba(120,90,60,.2));border:var(--cbd,none);
backdrop-filter:var(--sblur,none);-webkit-backdrop-filter:var(--sblur,none);
display:flex;align-items:center;justify-content:center}
#rnmask{position:fixed;inset:0;z-index:41;display:none;background:rgba(0,0,0,.25)}
#rnset{position:fixed;left:0;right:0;bottom:0;z-index:42;background:var(--card);
border-radius:var(--radius,18px) var(--radius,18px) 0 0;border:var(--cbd,none);
backdrop-filter:blur(18px);-webkit-backdrop-filter:blur(18px);
box-shadow:0 -6px 24px rgba(0,0,0,.18);padding:16px 16px 26px;max-height:78vh;
overflow-y:auto;display:none;max-width:640px;margin:0 auto}
#rnset.on,#rnmask.on{display:block}
#rnset h3{font-size:16px;margin-bottom:4px}
.rns{font-size:13px;color:var(--sub);margin:14px 0 6px}
.rnthg{display:grid;grid-template-columns:1fr 1fr;gap:8px}
.rnth{border:var(--cbd,1px solid var(--line,#e5dccb));border-radius:12px;padding:8px 10px;
font-size:14px;cursor:pointer;display:flex;align-items:center;gap:8px;background:var(--bg)}
.rnth.cur{outline:2px solid var(--accent)}
.rnth .dots{display:flex;gap:3px;margin-left:auto}
.rnth .dots i{width:12px;height:12px;border-radius:50%;display:block;border:1px solid rgba(0,0,0,.12)}
.rnrow{display:flex;gap:8px;flex-wrap:wrap;align-items:center}
.rnsw{width:26px;height:26px;border-radius:50%;cursor:pointer;border:1px solid rgba(0,0,0,.15)}
.rnsw.cur{outline:2.5px solid var(--accent);outline-offset:1px}
.rnpl{font-size:11px;color:var(--sub);width:100%;margin-top:4px}
.rnbt{padding:8px 14px;font-size:13px;border-radius:10px;background:var(--bg);
color:var(--ink);border:1px solid var(--line,#e5dccb)}
.rnbt.cur{background:var(--accent);color:#fff;border-color:var(--accent)}
.rnclr{width:44px;height:30px;border:1px solid var(--line,#e5dccb);border-radius:8px;
padding:0;background:none;cursor:pointer}
</style>"""

# 注入到每个页面：应用主题/夜间/四项颜色/字色/阅读背景/翻页方式 + 设置按钮与面板
# （阅读页不显示设置按钮，所有设置在书架页调好后进阅读页生效）
SETTINGS_SNIPPET = """<script>
const RNT=__TJSON__,RNPAL=__PJSON__;
const RNLS=k=>localStorage.getItem(k)||'';
function rnApply(){
 let k=RNLS('rn_theme');if(!RNT[k])k='puppy';
 const night=RNLS('rn_mode')==='night';
 const t=RNT[k];
 const r=document.documentElement.style;r.cssText='';
 const vars=Object.assign({},t.day,night?t.night:{});
 for(const[v,c]of Object.entries(vars))r.setProperty(v,c);
 if(document.body)document.body.className=document.body.className.replace(/\\bth-\\w+\\b/g,'').trim()+' th-'+k;
 const deco=night?(t.decoN||''):(t.deco||'');
 if(deco)r.setProperty('--bgfull','url("data:image/svg+xml,'+encodeURIComponent(deco)+'") repeat,'+vars['--bg']);
 if(t.sticker)r.setProperty('--sticker','"'+t.sticker+'"');
 if(RNLS('rn_mark_u'))r.setProperty('--mark-u',RNLS('rn_mark_u')+'66');
 if(RNLS('rn_mark_ai'))r.setProperty('--mark-ai',RNLS('rn_mark_ai')+'66');
 if(RNLS('rn_bub_u')){r.setProperty('--pink',RNLS('rn_bub_u')+'2e');
  r.setProperty('--pink-line',RNLS('rn_bub_u'));r.setProperty('--pink-ink',RNLS('rn_bub_u'));}
 if(RNLS('rn_bub_ai')){r.setProperty('--blue',RNLS('rn_bub_ai')+'2e');
  r.setProperty('--blue-line',RNLS('rn_bub_ai'));r.setProperty('--blue-ink',RNLS('rn_bub_ai'));}
 if(RNLS('rn_ink'))r.setProperty('--rink',RNLS('rn_ink'));
 const rb=RNLS('rn_rbg');
 if(rb==='white'){r.setProperty('--rbg','#ffffff');if(!RNLS('rn_ink'))r.setProperty('--rink','#333333');}
 else if(rb==='black'){r.setProperty('--rbg','#0e0e10');if(!RNLS('rn_ink'))r.setProperty('--rink','#cfcfcf');}
 else if(rb==='paper'){r.setProperty('--rbg','linear-gradient(rgba(120,90,50,.04),rgba(120,90,50,.1)),repeating-linear-gradient(0deg,rgba(120,90,50,.03) 0 1px,transparent 1px 28px),#f7efdc');
  if(!RNLS('rn_ink'))r.setProperty('--rink','#453b2c');}
 else if(rb==='custom')r.setProperty('--rbg','url("/bg?v='+RNLS('rn_bgv')+'") center/cover no-repeat fixed');
}
rnApply();
document.addEventListener('DOMContentLoaded',rnApply);
function rnSet(k,v){v?localStorage.setItem(k,v):localStorage.removeItem(k);rnApply();rnPanel();}
function rnPick(label,key,dflt){
 const cur=RNLS(key);
 let h='<div class="rns">'+label+'</div><div class="rnrow">'+
  '<button class="rnbt'+(cur?'':' cur')+'" onclick="rnSet(\\''+key+'\\',\\'\\')">跟随主题</button>'+
  '<input type="color" class="rnclr" value="'+(cur||dflt)+'" onchange="rnSet(\\''+key+'\\',this.value)"></div>';
 for(const[pn,cs]of Object.entries(RNPAL)){
  h+='<div class="rnrow"><span class="rnpl">'+pn+'</span>'+cs.map(c=>
   '<span class="rnsw'+(cur===c?' cur':'')+'" style="background:'+c+'" onclick="rnSet(\\''+key+'\\',\\''+c+'\\')"></span>').join('')+'</div>';}
 return h;
}
function rnPanel(){
 const p=document.getElementById('rnset');if(!p)return;
 const curT=RNT[RNLS('rn_theme')]?RNLS('rn_theme'):'puppy';
 const night=RNLS('rn_mode')==='night';
 let h='<h3>设置</h3><div class="rns">主题（'+(night?'夜间':'白天')+'）</div><div class="rnthg">';
 for(const[k,t]of Object.entries(RNT)){
  const v=night?Object.assign({},t.day,t.night):t.day;
  h+='<div class="rnth'+(k===curT?' cur':'')+'" onclick="rnSet(\\'rn_theme\\',\\''+k+'\\')">'+t.label+
   '<span class="dots"><i style="background:'+v['--bg'].split(' ')[0].replace('linear-gradient(135deg,','').replace(',','')+'"></i>'+
   '<i style="background:'+v['--accent']+'"></i><i style="background:'+v['--pink-line']+'"></i></span></div>';}
 h+='</div><div class="rns">白天 / 夜间</div><div class="rnrow">'+
  '<button class="rnbt'+(night?'':' cur')+'" onclick="rnSet(\\'rn_mode\\',\\'\\')">☀ 白天</button>'+
  '<button class="rnbt'+(night?' cur':'')+'" onclick="rnSet(\\'rn_mode\\',\\'night\\')">🌙 夜间</button></div>';
 const flow=RNLS('rn_flow')==='scroll',tap=RNLS('rn_tapturn')!=='off';
 h+='<div class="rns">阅读翻页方式</div><div class="rnrow">'+
  '<button class="rnbt'+(flow?'':' cur')+'" onclick="rnSet(\\'rn_flow\\',\\'\\')">左右翻页</button>'+
  '<button class="rnbt'+(flow?' cur':'')+'" onclick="rnSet(\\'rn_flow\\',\\'scroll\\')">上下滑动·无缝</button></div>';
 h+='<div class="rns">点击屏幕两侧翻页（左右翻页时）</div><div class="rnrow">'+
  '<button class="rnbt'+(tap?' cur':'')+'" onclick="rnSet(\\'rn_tapturn\\',\\'\\')">开</button>'+
  '<button class="rnbt'+(tap?'':' cur')+'" onclick="rnSet(\\'rn_tapturn\\',\\'off\\')">关</button></div>';
 h+=rnPick('我的划线色','rn_mark_u','#e8a0ac');
 h+=rnPick('__ANAME__回应后的划线色','rn_mark_ai','#7fa8d0');
 h+=rnPick('我的批注气泡色','rn_bub_u','#e8a0ac');
 h+=rnPick('__ANAME__的批注气泡色','rn_bub_ai','#7fa8d0');
 h+=rnPick('阅读正文字色','rn_ink','#3d3630');
 const rb=RNLS('rn_rbg');
 h+='<div class="rns">阅读页背景</div><div class="rnrow">'+
  [['','跟随主题'],['white','纯白'],['paper','书页'],['black','纯黑']].map(([v,n])=>
   '<button class="rnbt'+(rb===v?' cur':'')+'" onclick="rnSet(\\'rn_rbg\\',\\''+v+'\\')">'+n+'</button>').join('')+
  '<button class="rnbt'+(rb==='custom'?' cur':'')+'" onclick="document.getElementById(\\'rnbgf\\').click()">🖼 上传图片</button>'+
  '<input type="file" id="rnbgf" accept="image/*" hidden></div>';
 h+='<div class="rns"></div><button class="rnbt" onclick="rnReset()">恢复全部默认</button>'+
  '<span id="rnst" style="font-size:12px;color:var(--sub);margin-left:10px"></span>';
 p.innerHTML=h;
 const f=document.getElementById('rnbgf');
 if(f)f.onchange=async e=>{
  const file=e.target.files[0];if(!file)return;
  document.getElementById('rnst').textContent='上传中…';
  const r=await fetch('/api/bg',{method:'POST',body:file}).then(r=>r.json());
  if(r.ok){localStorage.setItem('rn_bgv',Date.now());rnSet('rn_rbg','custom');}
  else document.getElementById('rnst').textContent='✗ '+(r.error||'失败');
 };
}
function rnReset(){['rn_theme','rn_mode','rn_mark','rn_mark_u','rn_mark_ai','rn_bub_u','rn_bub_ai','rn_ink','rn_rbg','rn_flow','rn_tapturn'].forEach(k=>localStorage.removeItem(k));rnApply();rnPanel();}
document.addEventListener('DOMContentLoaded',()=>{
 if(document.querySelector('.gate'))return;
 if(document.getElementById('bot'))return; /* 阅读页不放设置按钮 */
 const fab=document.createElement('button');fab.id='rnfab';fab.textContent='⚙';
 const mask=document.createElement('div');mask.id='rnmask';
 const panel=document.createElement('div');panel.id='rnset';
 fab.onclick=()=>{rnPanel();panel.classList.add('on');mask.classList.add('on');};
 mask.onclick=()=>{panel.classList.remove('on');mask.classList.remove('on');};
 document.body.append(fab,mask,panel);
});
</script>""".replace("__TJSON__", json.dumps(THEMES, ensure_ascii=False)) \
            .replace("__PJSON__", json.dumps(PALETTES, ensure_ascii=False))

# ---------------- 页面模板 ----------------

BASE_CSS = """
:root{--bg:#faf6ef;--card:#fffdf8;--ink:#3d3630;--sub:#9b8f80;--accent:#c96f4a;
--pink:#fdeef0;--pink-line:#e8a0ac;--blue:#e8f1fa;--blue-line:#7fa8d0;--mark:#f9e3c8;
--pink-ink:#b05a68;--blue-ink:#4a6f96;--line:#eee2d4}
*{box-sizing:border-box;margin:0;padding:0;-webkit-tap-highlight-color:transparent}
body{background:var(--bg);color:var(--ink);
font-family:var(--font,'Noto Serif SC',Georgia,serif);font-size:17px;line-height:1.9}
a{color:var(--accent);text-decoration:none}
.wrap{max-width:640px;margin:0 auto;padding:16px}
button{font-family:inherit;cursor:pointer;border:none;border-radius:10px}
"""

LOGIN_HTML = """<!doctype html><html lang="zh"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>共读小屋</title><style>__CSS__
.gate{min-height:100vh;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:20px}
input{font-size:22px;letter-spacing:8px;text-align:center;width:180px;padding:10px;
border:2px solid var(--pink-line);border-radius:12px;background:var(--card);color:var(--ink);outline:none}
.hint{color:var(--sub);font-size:14px}
</style></head><body><div class="gate">
<div style="font-size:40px">📖</div><div>共读小屋</div>
<input id="pc" type="tel" maxlength="4" placeholder="····" autofocus>
<div class="hint">__HINT__</div>
</div><script>
const pc=document.getElementById('pc');
pc.addEventListener('input',()=>{if(pc.value.length===4){
document.cookie='rk='+pc.value+';path=/;max-age=31536000';location.reload();}});
</script></body></html>"""

HOME_HTML = """<!doctype html><html lang="zh"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>共读小屋</title><style>__CSS__
h1{font-size:22px;padding:18px 0 4px;text-align:center}
.sub{text-align:center;color:var(--sub);font-size:13px;margin-bottom:20px}
.card{background:var(--card);border-radius:16px;padding:16px;margin-bottom:14px;
box-shadow:0 1px 6px rgba(120,90,60,.08)}
.bt{font-size:18px;font-weight:600;margin-bottom:2px}
.bm{color:var(--sub);font-size:13px;margin-bottom:12px}
.modes{display:flex;gap:10px}
.modes button{flex:1;padding:12px 6px;font-size:15px}
.m1{background:var(--mark);color:var(--ink)}
.m2{background:var(--pink);color:var(--pink-ink);border:1px solid var(--pink-line)}
.cont{margin-top:10px;font-size:13px;color:var(--accent)}
.up{border:2px dashed var(--pink-line);background:none;text-align:center;padding:26px;
border-radius:16px;color:var(--sub);width:100%;font-size:15px}
.empty{text-align:center;color:var(--sub);padding:30px 0}
#st{text-align:center;color:var(--accent);font-size:14px;min-height:20px;margin-top:8px}
</style></head><body><div class="wrap">
<h1>📖 共读小屋</h1><div class="sub">__SUB__</div>
<div id="books"></div>
<input type="file" id="f" hidden>
<button class="up" onclick="document.getElementById('f').click()">＋ 传一本新书（txt 文件）</button>
<button class="up" style="margin-top:8px" onclick="var b=document.getElementById('paste');b.style.display=b.style.display==='none'?'block':'none'">✍️ 直接粘贴文字（不用文件）</button>
<div id="paste" style="display:none;margin-top:10px">
<input id="pt" placeholder="书名" style="width:100%;padding:12px;border:1px solid var(--pink-line);border-radius:12px;font-size:15px;background:none;color:var(--ink);box-sizing:border-box">
<textarea id="pb" rows="10" placeholder="把正文粘在这里。章节标题各占一行，比如「第一章 逃跑」。可以分几次粘，粘完再存。" style="width:100%;margin-top:8px;padding:12px;border:1px solid var(--pink-line);border-radius:12px;font-size:14px;line-height:1.7;background:none;color:var(--ink);box-sizing:border-box"></textarea>
<div style="text-align:right;font-size:12px;color:var(--sub);margin-top:4px"><span id="pc">0</span> 字</div>
<button class="up" style="padding:14px;margin-top:4px" onclick="savePaste()">存进书架</button>
</div>
<div id="st"></div>
<div style="display:flex;gap:10px;margin-top:16px">
<button style="flex:1;padding:12px;background:var(--blue);border:1px solid var(--blue-line);color:var(--blue-ink);font-size:14px" onclick="location.href='/ds'">DeepSeek工作台🖥️</button>
<button style="flex:1;padding:12px;background:var(--mark);color:var(--ink);font-size:14px" onclick="location.href='/gardener'">🌙 记忆园丁</button>
</div>
</div><script>
async function load(){
 const [books,prog]=await Promise.all([
   fetch('/api/books').then(r=>r.json()),
   fetch('/api/progress').then(r=>r.json())]);
 const el=document.getElementById('books');
 if(!books.length){el.innerHTML='<div class="empty">书架还空着，传一本书开始吧</div>';return;}
 el.innerHTML=books.map(b=>{
  const p=prog[b.slug];
  const cont=p?`<div class="cont" onclick="go('${b.slug}',${p.ch},${p.mode})">▸ 继续读：${b.chapters[p.ch]}（${p.mode===2?'批注模式':'阅读模式'}）</div>`:'';
  return `<div class="card"><div class="bt">${b.title}<span onclick="delBook(event,'${b.slug}','${b.title.replace(/'/g,"\\'")}')" style="float:right;cursor:pointer;color:var(--sub);font-size:13px;padding:0 4px">删</span></div>
  <div class="bm">${b.chapters.length} 章 · ${b.created}</div>
  <div class="modes">
   <button class="m1" onclick="go('${b.slug}',${p?p.ch:0},1)">功能一 · 纯阅读</button>
   <button class="m2" onclick="go('${b.slug}',${p?p.ch:0},2)">功能二 · 批注共读</button>
  </div>${cont}</div>`;}).join('');
}
function go(s,c,m){location.href='/read/'+encodeURIComponent(s)+'/'+c+'?mode='+m;}
async function delBook(e,slug,title){
 e.stopPropagation();
 if(!confirm('删掉《'+title+'》？\n\n它的章节和你在上面写的批注会一起没掉，删了找不回来。'))return;
 const st=document.getElementById('st');st.textContent='删除中…';
 const r=await fetch('/api/delete',{method:'POST',
  headers:{'Content-Type':'application/json'},body:JSON.stringify({slug:slug})});
 const j=await r.json();
 st.textContent=j.ok?('✓ 已删：'+j.title):('✗ '+j.error);
 load();
}
document.getElementById('pb').addEventListener('input',e=>{
 document.getElementById('pc').textContent=e.target.value.length;});
async function savePaste(){
 const t=document.getElementById('pt').value.trim();
 const b=document.getElementById('pb').value;
 const st=document.getElementById('st');
 if(!t){st.textContent='✗ 先给它起个书名';return;}
 if(!b.trim()){st.textContent='✗ 正文是空的';return;}
 st.textContent='存进去中…';
 const r=await fetch('/api/upload',{method:'POST',
  headers:{'X-Filename':encodeURIComponent(t+'.txt')},body:new Blob([b],{type:'text/plain'})});
 const j=await r.json();
 if(j.ok){st.textContent='✓ 已入库：'+j.title+'（'+j.count+' 章）';
  document.getElementById('pb').value='';document.getElementById('pt').value='';
  document.getElementById('pc').textContent='0';
  document.getElementById('paste').style.display='none';}
 else st.textContent='✗ '+j.error;
 load();
}
document.getElementById('f').addEventListener('change',async e=>{
 const file=e.target.files[0];if(!file)return;
 const st=document.getElementById('st');st.textContent='上传中…';
 const r=await fetch('/api/upload',{method:'POST',
  headers:{'X-Filename':encodeURIComponent(file.name)},body:file});
 const j=await r.json();
 st.textContent=j.ok?('✓ 已入库：'+j.title+'（'+j.count+' 章）'):('✗ '+j.error);
 load();
});
load();
</script></body></html>"""

READER_HTML = """<!doctype html><html lang="zh"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,user-scalable=no">
<title>阅读</title><style>__CSS__
body{overflow:hidden;background:var(--rbg,var(--bgfull,var(--bg)))}
#top{position:fixed;top:0;left:0;right:0;background:var(--rbg,var(--bgfull,var(--bg)));z-index:5;
display:flex;align-items:center;gap:8px;padding:10px 14px;font-size:13px;color:var(--sub)}
#top a{font-size:15px}
#ct{flex:1;text-align:center;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#page{position:fixed;top:44px;bottom:52px;left:0;right:0;overflow-y:auto;
padding:8px 22px 20px;max-width:680px;margin:0 auto;color:var(--rink,var(--ink))}
#page p{text-indent:2em;margin-bottom:.9em}
.chdiv{text-align:center;color:var(--sub);font-size:14px;margin:30px 0 20px;letter-spacing:3px}
mark{background:var(--mark);border-bottom:2px solid var(--accent);padding:1px 0;cursor:pointer}
mark.mu{background:var(--mark-u,var(--mark))}
mark.mr{background:var(--mark-ai,var(--mark))}
mark .dot{display:inline-block;width:8px;height:8px;border-radius:50%;margin-left:2px;vertical-align:super}
mark .du{background:var(--pink-line)}mark .dr{background:var(--blue-line)}
#bot{position:fixed;bottom:0;left:0;right:0;background:var(--rbg,var(--bg));z-index:5;
display:flex;align-items:center;justify-content:space-between;padding:8px 18px;
font-size:14px;color:var(--sub)}
#bot button{background:none;font-size:15px;color:var(--accent);padding:6px 14px}
#tool{position:fixed;display:none;z-index:20;background:#2c2c34;border-radius:10px;
padding:6px;gap:6px}
#tool button{background:none;color:#fff;font-size:14px;padding:6px 10px}
.sheet{position:fixed;left:0;right:0;bottom:0;z-index:30;background:var(--card);
border-radius:18px 18px 0 0;box-shadow:0 -4px 20px rgba(0,0,0,.15);padding:16px;
max-height:70vh;overflow-y:auto;display:none}
.sheet.on{display:block}
.quote{font-size:13px;color:var(--sub);border-left:3px solid var(--pink-line);
padding-left:8px;margin-bottom:10px}
.bub{border-radius:12px;padding:9px 12px;margin-bottom:8px;font-size:15px;max-width:88%}
.bu{background:var(--pink);border:1px solid var(--pink-line);margin-left:auto}
.br{background:var(--blue);border:1px solid var(--blue-line)}
.who{font-size:11px;color:var(--sub);margin-bottom:2px}
.sheet textarea{width:100%;border:1px solid var(--pink-line);border-radius:10px;
padding:9px;font-family:inherit;font-size:15px;background:var(--bg);color:var(--ink);
resize:none;height:70px;outline:none}
.srow{display:flex;gap:10px;margin-top:8px}
.srow button{flex:1;padding:10px;font-size:15px}
.ok{background:var(--pink);color:var(--pink-ink);border:1px solid var(--pink-line)}
.cc{background:none;color:var(--sub)}
.del{background:none;color:var(--sub);font-size:12px;margin-top:4px}
#mask{position:fixed;inset:0;z-index:25;display:none;background:rgba(0,0,0,.2)}
#mask.on{display:block}
#alist{position:fixed;top:44px;bottom:52px;right:0;width:82%;max-width:340px;z-index:26;
background:var(--card);box-shadow:-3px 0 16px rgba(0,0,0,.12);padding:14px;
overflow-y:auto;display:none}
#alist.on{display:block}
.ai{border-bottom:1px solid var(--line);padding:10px 0;font-size:14px;cursor:pointer}
.ai .q{color:var(--sub);font-size:12px}
.ai.cur{color:var(--accent);font-weight:600}
</style></head><body>
<div id="top"><a href="/">〈 书架</a><div id="ct"></div>
<span id="tbtn" style="cursor:pointer;margin-right:12px;font-size:17px">☰</span>
<span id="abtn" style="display:none;cursor:pointer">💬<span id="acnt"></span></span></div>
<div id="page"></div>
<div id="bot"><button onclick="nav(-1)">‹ 上一页</button>
<span id="pg"></span><button onclick="nav(1)">下一页 ›</button></div>
<div id="tool"><button onclick="mk('')">🖊 划线</button><button onclick="mk(null)">💭 写想法</button></div>
<div id="mask" onclick="closeAll()"></div>
<div id="alist"></div>
<div class="sheet" id="sh"></div>
<script>
const SLUG=__SLUG__,CH=__CH__,MODE=__MODE__;
const FLOW=localStorage.getItem('rn_flow')==='scroll';
const TAP=localStorage.getItem('rn_tapturn')!=='off';
let pages=[],cur=0,data=null,pendAnchor=null,pendCh=CH;
let loaded=[],loading=false,saveT=0;
const $=id=>document.getElementById(id);
function esc(s){return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');}
function paginate(paras){
 const ps=[];let buf=[],n=0;
 for(const p of paras){buf.push(p);n+=p.length;
  if(n>=1100){ps.push(buf);buf=[];n=0;}}
 if(buf.length)ps.push(buf);
 return ps.length?ps:[['（本章为空）']];
}
async function fetchCh(i){
 const d=await fetch('/api/chapter/'+encodeURIComponent(SLUG)+'/'+i).then(r=>r.json());
 const annos=MODE===2?await fetch('/api/annotations/'+encodeURIComponent(SLUG)+'/'+i).then(r=>r.json()):[];
 const paras=d.text.split('\\n').map(s=>s.trim()).filter(Boolean);
 return {ch:i,title:d.title,paras:paras.length?paras:['（本章为空）'],annos:annos,pages:paginate(paras),data:d};
}
async function init(){
 const first=await fetchCh(CH);
 data=first.data;loaded=[first];pages=first.pages;
 if(MODE===2)$('abtn').style.display='inline';
 $('ct').textContent=first.title;
 const prog=await fetch('/api/progress').then(r=>r.json());
 const p=prog[SLUG];
 if(FLOW){
  renderScroll();
  if(p&&p.ch===CH&&pages.length>1){
   const el=$('page');
   requestAnimationFrame(()=>{el.scrollTop=(p.page/pages.length)*Math.max(0,el.scrollHeight-el.clientHeight);});
  }
  $('page').addEventListener('scroll',onScroll,{passive:true});
 }else{
  if(p&&p.ch===CH&&p.page<pages.length)cur=p.page;
  render();
 }
}
function chHtml(L){
 return '<div class="chb" data-ch="'+L.ch+'">'+
  (L.ch!==CH?'<div class="chdiv">'+esc(L.title)+'</div>':'')+
  L.paras.map(p=>'<p>'+deco(p,L.annos)+'</p>').join('')+'</div>';
}
function renderScroll(){
 const el=$('page'),st=el.scrollTop;
 el.innerHTML=loaded.map(chHtml).join('');
 el.scrollTop=st;updPg();
}
function topChb(){
 const el=$('page');let cb=null;
 el.querySelectorAll('.chb').forEach(b=>{if(b.offsetTop<=el.scrollTop+60)cb=b;});
 return cb||el.querySelector('.chb');
}
function onScroll(){
 const el=$('page');
 if(!loading&&el.scrollTop+el.clientHeight>el.scrollHeight-600){
  const last=loaded[loaded.length-1];
  if(last.ch+1<data.total){loading=true;
   fetchCh(last.ch+1).then(L=>{loaded.push(L);
    el.insertAdjacentHTML('beforeend',chHtml(L));loading=false;updPg();});}
 }
 clearTimeout(saveT);saveT=setTimeout(saveScrollProg,400);
 updPg();
}
function saveScrollProg(){
 const el=$('page'),b=topChb();if(!b)return;
 const L=loaded.find(x=>x.ch==b.dataset.ch);if(!L)return;
 const rc=Math.min(1,Math.max(0,(el.scrollTop-b.offsetTop)/Math.max(1,b.offsetHeight-el.clientHeight)));
 fetch('/api/progress',{method:'POST',headers:{'Content-Type':'application/json'},
  body:JSON.stringify({slug:SLUG,ch:L.ch,page:Math.min(L.pages.length-1,Math.floor(rc*L.pages.length)),mode:MODE})});
}
function updPg(){
 if(FLOW){
  const b=topChb();
  if(b){const L=loaded.find(x=>x.ch==b.dataset.ch);
   if(L)$('ct').textContent=L.title;
   $('pg').textContent=(+b.dataset.ch+1)+' / '+data.total+' 章';}
 }else $('pg').textContent=(cur+1)+' / '+pages.length;
 $('acnt').textContent=MODE===2?(loaded.reduce((s,L)=>s+L.annos.length,0)||''):'';
}
function render(){
 const el=$('page');
 el.innerHTML='<div class="chb" data-ch="'+CH+'">'+
  pages[cur].map(p=>'<p>'+deco(p,loaded[0].annos)+'</p>').join('')+'</div>';
 el.scrollTop=0;updPg();
 fetch('/api/progress',{method:'POST',headers:{'Content-Type':'application/json'},
  body:JSON.stringify({slug:SLUG,ch:CH,page:cur,mode:MODE})});
}
function deco(para,annos){
 if(MODE!==2)return esc(para);
 let hits=annos.filter(a=>para.includes(a.anchor));
 if(!hits.length)return esc(para);
 const a=hits[0];
 const i=para.indexOf(a.anchor);
 const rep=a.replies&&a.replies.length;
 return esc(para.slice(0,i))+'<mark class="'+(rep?'mr':'mu')+'" data-id="'+a.id+'">'+esc(a.anchor)+
  '<span class="dot '+(rep?'dr':'du')+'"></span></mark>'+deco(para.slice(i+a.anchor.length),annos);
}
function nav(d){
 if(FLOW){
  const b=topChb();const c=(b?+b.dataset.ch:CH)+d;
  if(c>=0&&c<data.total)location.href='/read/'+encodeURIComponent(SLUG)+'/'+c+'?mode='+MODE;
  return;
 }
 const c=cur+d;
 if(c<0){if(CH>0)location.href='/read/'+encodeURIComponent(SLUG)+'/'+(CH-1)+'?mode='+MODE;return;}
 if(c>=pages.length){
  if(CH+1<data.total)location.href='/read/'+encodeURIComponent(SLUG)+'/'+(CH+1)+'?mode='+MODE;
  return;}
 cur=c;render();
}
document.addEventListener('keydown',e=>{
 if(e.key==='ArrowLeft')nav(-1);if(e.key==='ArrowRight')nav(1);});
/* 点击屏幕两侧翻页（左右翻页模式；点到划线/链接不触发） */
if(!FLOW&&TAP){
 $('page').addEventListener('click',e=>{
  if(e.target.closest('mark')||e.target.closest('a'))return;
  const s=window.getSelection();
  if(s&&!s.isCollapsed)return;
  const x=e.clientX,w=window.innerWidth;
  if(x<w*0.28)nav(-1);
  else if(x>w*0.72)nav(1);
 });
}

/* -------- 批注 -------- */
function selInfo(){
 const s=window.getSelection();
 if(!s||s.isCollapsed)return null;
 const t=s.toString().trim();
 if(!t||t.length<2||t.length>300)return null;
 if(!$('page').contains(s.anchorNode))return null;
 return {text:t,rect:s.getRangeAt(0).getBoundingClientRect(),node:s.anchorNode};
}
if(MODE===2){
 document.addEventListener('selectionchange',()=>{setTimeout(showTool,180);});
 $('page').addEventListener('click',e=>{
  const m=e.target.closest('mark');
  if(m)openAnno(m.dataset.id);});
}
function showTool(){
 const info=selInfo(),t=$('tool');
 if(!info){t.style.display='none';return;}
 pendAnchor=info.text;
 const nd=info.node.nodeType===1?info.node:info.node.parentElement;
 const cb=nd&&nd.closest?nd.closest('.chb'):null;
 pendCh=cb?+cb.dataset.ch:CH;
 t.style.display='flex';
 t.style.left=Math.max(8,Math.min(info.rect.left,window.innerWidth-150))+'px';
 let top=info.rect.bottom+14;
 if(top>window.innerHeight-110)top=Math.max(50,info.rect.top-46);
 t.style.top=top+'px';
}
function mk(note){
 $('tool').style.display='none';
 const anchor=pendAnchor;if(!anchor)return;
 window.getSelection().removeAllRanges();
 if(note===null){openEditor(anchor);return;}
 saveAnno(anchor,'');
}
function openEditor(anchor){
 const sh=$('sh');
 sh.innerHTML='<div class="quote">'+esc(anchor)+'</div>'+
  '<textarea id="nt" placeholder="想说什么…"></textarea>'+
  '<div class="srow"><button class="cc" onclick="closeAll()">算了</button>'+
  '<button class="ok" onclick="saveAnno(pendCache,document.getElementById(\\'nt\\').value)">存下来 ♡</button></div>';
 window.pendCache=anchor;
 sh.classList.add('on');$('mask').classList.add('on');
 setTimeout(()=>$('nt').focus(),100);
}
async function reloadAnnos(ch){
 const L=loaded.find(x=>x.ch===ch);
 if(L)L.annos=await fetch('/api/annotations/'+encodeURIComponent(SLUG)+'/'+ch).then(r=>r.json());
}
async function saveAnno(anchor,note){
 const ch=pendCh;
 await fetch('/api/annotations/'+encodeURIComponent(SLUG)+'/'+ch,{method:'POST',
  headers:{'Content-Type':'application/json'},
  body:JSON.stringify({anchor:anchor,note:note,who:'user'})});
 await reloadAnnos(ch);
 closeAll();FLOW?renderScroll():render();
}
function findAnno(id){
 for(const L of loaded){const a=L.annos.find(x=>x.id===id);if(a)return{a:a,L:L};}
 return null;
}
function openAnno(id){
 const f=findAnno(id);if(!f)return;
 const group=f.L.annos.filter(x=>x.anchor===f.a.anchor);
 const sh=$('sh');
 let h='<div class="quote">'+esc(f.a.anchor)+'</div>';
 let anyReply=false;
 for(const a of group){
  if(a.note)h+='<div class="bub bu"><div class="who">__UNAME__</div>'+esc(a.note)+'</div>';
  else h+='<div class="bub bu"><div class="who">__UNAME__</div>🖊 划了线</div>';
  for(const r of (a.replies||[])){anyReply=true;
   h+='<div class="bub br"><div class="who">__ANAME__</div>'+esc(r.text)+'</div>';}
  h+='<button class="del" onclick="delAnno(\\''+a.id+'\\')">删除这条</button>';
 }
 if(!anyReply)
  h+='<div style="font-size:12px;color:var(--sub)">__ANAME__ 还没看到，聊天里戳他一下～</div>';
 sh.innerHTML=h;sh.classList.add('on');$('mask').classList.add('on');
}
async function delAnno(id){
 const f=findAnno(id);if(!f)return;
 await fetch('/api/annotations/'+encodeURIComponent(SLUG)+'/'+f.L.ch+'?id='+id,{method:'DELETE'});
 await reloadAnnos(f.L.ch);
 closeAll();FLOW?renderScroll():render();
}
$('tbtn').onclick=()=>{
 const el=$('alist');
 el.innerHTML='<div style="font-weight:600;margin-bottom:6px">目录</div>'+
  data.chapters.map((t,i)=>'<div class="ai toc'+(i===CH?' cur':'')+'" data-i="'+i+'">'+esc(t)+'</div>').join('');
 el.querySelectorAll('.toc').forEach(d=>{d.onclick=()=>{
  location.href='/read/'+encodeURIComponent(SLUG)+'/'+d.dataset.i+'?mode='+MODE;};});
 el.classList.add('on');$('mask').classList.add('on');
 const c=el.querySelector('.cur');if(c)c.scrollIntoView({block:'center'});
};
$('abtn').onclick=()=>{
 const el=$('alist');
 const all=[];
 for(const L of loaded)for(const a of L.annos)all.push(a);
 el.innerHTML=all.length?all.map(a=>
  '<div class="ai" onclick="closeAll();openAnno(\\''+a.id+'\\')">'+
  '<div class="q">'+esc(a.anchor.slice(0,40))+'</div>'+
  esc(a.note||'🖊 划线')+(a.replies&&a.replies.length?' <span style="color:var(--blue-line)">· __ANAME__回了</span>':'')+
  '</div>').join(''):'<div style="color:var(--sub);text-align:center;padding:20px">这一章还没有批注</div>';
 el.classList.add('on');$('mask').classList.add('on');
};
function closeAll(){
 $('sh').classList.remove('on');$('alist').classList.remove('on');
 $('mask').classList.remove('on');$('tool').style.display='none';
}
init();
</script></body></html>"""


DS_HTML = """<!doctype html><html lang="zh"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>DeepSeek工作台</title><style>__CSS__
h1{font-size:20px;padding:14px 0;text-align:center}
.stat{display:flex;gap:10px;margin-bottom:14px}
.stat div{flex:1;background:var(--card);border-radius:12px;padding:10px;text-align:center}
.stat b{display:block;font-size:20px;color:var(--accent)}
.stat span{font-size:12px;color:var(--sub)}
.item{background:var(--card);border-radius:12px;padding:10px 12px;margin-bottom:8px;font-size:14px}
.item .t{display:flex;justify-content:space-between;color:var(--sub);font-size:12px}
.tag{display:inline-block;padding:1px 8px;border-radius:8px;font-size:12px;margin-right:6px}
.tg1{background:var(--mark)}.tg2{background:var(--pink);color:var(--pink-ink)}
.tg3{background:var(--blue);color:var(--blue-ink)}.tgx{background:#f3d6d6;color:#a04040}
.sec{font-size:15px;font-weight:600;margin:18px 0 8px;color:var(--sub)}
.note-item{cursor:pointer}
#nview{background:var(--card);border-radius:12px;padding:14px;font-size:14px;
white-space:pre-wrap;display:none;margin-bottom:10px;border:1px solid var(--blue-line)}
a.back{display:block;padding:12px 0}
</style></head><body><div class="wrap">
<a class="back" href="/">〈 书架</a>
<h1>DeepSeek 工作台</h1>
<div class="stat" id="stat"></div>
<div class="sec">📖 剧情笔记（点章节查看）</div>
<div id="notes"></div>
<div id="nview"></div>
<div class="sec">📋 调用日志（最近在前）</div>
<div id="log"></div>
</div><script>
const tagCls={'拆章判断':'tg1','剧情笔记':'tg2','调用':'tg3'};
async function load(){
 const [log,books]=await Promise.all([
  fetch('/api/dslog').then(r=>r.json()),
  fetch('/api/books').then(r=>r.json())]);
 const ok=log.filter(e=>e.ok);
 const tin=ok.reduce((s,e)=>s+(e.tokens_in||0),0), tout=ok.reduce((s,e)=>s+(e.tokens_out||0),0);
 const cost=(tin/1e6*2+tout/1e6*8).toFixed(3);
 document.getElementById('stat').innerHTML=
  `<div><b>${log.length}</b><span>总调用</span></div>
   <div><b>${((tin+tout)/1000).toFixed(1)}k</b><span>总tokens</span></div>
   <div><b>¥${cost}</b><span>估算花费</span></div>`;
 let nh='';
 for(const b of books){
  const st=await fetch('/api/noteslist/'+encodeURIComponent(b.slug)).then(r=>r.json());
  nh+=`<div class="item"><b>${b.title}</b> <span style="color:var(--sub);font-size:12px">笔记 ${st.have}/${b.chapters.length} 章</span>
   <div style="margin-top:6px">`+
   b.chapters.map((t,i)=>st.list.includes(i)?
    `<span class="tag tg2 note-item" onclick="showNote('${b.slug}',${i})">${i}</span>`:'').join(' ')+
   `</div></div>`;
 }
 document.getElementById('notes').innerHTML=nh||'<div class="item">还没有笔记</div>';
 document.getElementById('log').innerHTML=log.slice().reverse().map(e=>
  `<div class="item"><span class="tag ${e.ok?(tagCls[e.task]||'tg3'):'tgx'}">${e.task}${e.ok?'':' ✗'}</span>${e.detail||''}
   <div class="t"><span>${e.ok?((e.tokens_in||0)+'+'+(e.tokens_out||0)+' tok · '+(e.secs||'?')+'s'):(e.error||'失败')}</span><span>${e.ts}</span></div></div>`
 ).join('')||'<div class="item">暂无记录</div>';
}
async function showNote(slug,i){
 const d=await fetch('/api/note/'+encodeURIComponent(slug)+'/'+i).then(r=>r.json());
 const v=document.getElementById('nview');
 v.textContent=d.note||'（无）';v.style.display='block';
 v.scrollIntoView({behavior:'smooth'});
}
load();
</script></body></html>"""

GARDENER_HTML = """<!doctype html><html lang="zh"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>记忆园丁</title><style>__CSS__
h1{font-size:20px;padding:14px 0;text-align:center}
.card{background:var(--card);border-radius:14px;padding:12px 14px;margin-bottom:10px;font-size:14px}
.day{color:var(--accent);font-weight:600;margin-bottom:6px}
.act{padding:4px 0;border-bottom:1px dashed var(--line)}
.act:last-child{border-bottom:none}
.meta{color:var(--sub);font-size:12px;margin-top:6px}
a.back{display:block;padding:12px 0}
.info{background:var(--mark);border-radius:12px;padding:10px 14px;font-size:13px;margin-bottom:14px}
</style></head><body><div class="wrap">
<a class="back" href="/">〈 书架</a>
<h1>🌙 记忆园丁</h1>
<div class="info">每天早上5:30自动整理OB记忆：过期一次性事件沉底、重复桶留新不留旧。沉底≠删除，关键词仍可检索，dashboard可恢复。每次干完活会发TG报告。</div>
<div id="runs"></div>
</div><script>
fetch('/api/gardener').then(r=>r.json()).then(runs=>{
 document.getElementById('runs').innerHTML=runs.length?runs.slice().reverse().map(r=>
  `<div class="card"><div class="day">${r.ts}</div>`+
  (r.actions.length?r.actions.map(a=>`<div class="act">${a}</div>`).join(''):'<div class="act" style="color:var(--sub)">检查了一遍，没有需要整理的</div>')+
  `<div class="meta">候选桶 ${r.candidates}${r.tokens_in?' · DeepSeek '+r.tokens_in+'+'+(r.tokens_out||0)+' tok':''}${r.manual?' · 手动执行':''}</div></div>`
 ).join(''):'<div class="card">园丁还没干过活，今晚5:30第一次上岗</div>';
});
</script></body></html>"""


def render(tpl, **kw):
    html = tpl.replace("__CSS__", BASE_CSS)
    # 结构样式追加在页面CSS之后（获得覆盖权），设置脚本注入body开头
    html = html.replace("</head>", EXTRA_CSS + "</head>", 1)
    html = html.replace("<body>", "<body>" + SETTINGS_SNIPPET, 1)
    # 全局个人化占位符（来自 config.json）
    html = (html.replace("__SUB__", SUBTITLE).replace("__HINT__", LOGIN_HINT)
                .replace("__UNAME__", USER_NAME).replace("__ANAME__", AI_NAME))
    for k, v in kw.items():
        html = html.replace(f"__{k}__", v)
    return html


# ---------------- HTTP ----------------

# 密码尝试限速：同IP 10分钟内错5次 → 封30分钟（4位数密码必须防暴力枚举）
_fails = {}
_fails_lock = threading.Lock()


def _client_blocked(ip):
    with _fails_lock:
        rec = _fails.get(ip)
        if not rec:
            return False
        tries, until = rec
        if until and time.time() < until:
            return True
        if until and time.time() >= until:
            del _fails[ip]
        return False


def _record_fail(ip):
    with _fails_lock:
        tries, until = _fails.get(ip, (0, 0))
        tries += 1
        if tries >= 5:
            _fails[ip] = (0, time.time() + 1800)
        else:
            _fails[ip] = (tries, 0)


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass

    # -- helpers --
    def send_html(self, html, code=200):
        body = html.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def send_json(self, obj, code=200):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def authed(self):
        ip = self.client_address[0]
        if ip != "127.0.0.1" and _client_blocked(ip):
            return False
        cookies = self.headers.get("Cookie", "")
        if f"rk={PASSCODE}" in cookies:
            return True
        # 带了错误密码才算一次尝试（无cookie的新访客不算）
        m = re.search(r"rk=(\d+)", cookies)
        if m and m.group(1) != PASSCODE:
            _record_fail(ip)
        return False

    def body(self):
        n = int(self.headers.get("Content-Length", 0) or 0)
        return self.rfile.read(n) if n else b""

    # -- routes --
    def do_GET(self):
        u = urlparse(self.path)
        path = unquote(u.path)
        qs = dict(p.split("=", 1) for p in u.query.split("&") if "=" in p)

        if not self.authed():
            if path.startswith("/api/"):
                return self.send_json({"error": "unauthorized"}, 401)
            return self.send_html(render(LOGIN_HTML))

        if path == "/":
            return self.send_html(render(HOME_HTML))

        if path == "/ds":
            return self.send_html(render(DS_HTML))

        if path == "/gardener":
            return self.send_html(render(GARDENER_HTML))

        if path == "/api/dslog":
            return self.send_json(load_json(DS_LOG, []))

        if path == "/api/gardener":
            return self.send_json(load_json(GARDENER_LOG, []) if GARDENER_LOG else [])

        m = re.match(r"^/api/noteslist/([^/]+)$", path)
        if m:
            ndir = os.path.join(BOOKS_DIR, m.group(1), "notes")
            lst = sorted(int(f[:3]) for f in os.listdir(ndir)
                         if f.endswith(".md")) if os.path.isdir(ndir) else []
            return self.send_json({"have": len(lst), "list": lst})

        m = re.match(r"^/read/([^/]+)/(\d+)$", path)
        if m:
            slug, idx = m.group(1), int(m.group(2))
            mode = 2 if qs.get("mode") == "2" else 1
            if not get_chapter(slug, idx):
                return self.send_html("<h3>没找到这一章</h3>", 404)
            return self.send_html(render(
                READER_HTML,
                SLUG=json.dumps(slug, ensure_ascii=False),
                CH=str(idx), MODE=str(mode)))

        if path == "/api/books":
            return self.send_json(list_books())

        if path == "/api/progress":
            return self.send_json(load_json(PROGRESS_FILE, {}))

        m = re.match(r"^/api/chapter/([^/]+)/(\d+)$", path)
        if m:
            ch = get_chapter(m.group(1), int(m.group(2)))
            return self.send_json(ch) if ch else self.send_json({"error": "not found"}, 404)

        m = re.match(r"^/api/annotations/([^/]+)/(\d+)$", path)
        if m:
            return self.send_json(load_json(anno_path(m.group(1), int(m.group(2))), []))

        # 章节剧情笔记（DeepSeek预读生成，供AI伴读快速恢复上下文）
        m = re.match(r"^/api/note/([^/]+)/(\d+)$", path)
        if m:
            np = note_path(m.group(1), int(m.group(2)))
            if os.path.exists(np):
                with open(np, encoding="utf-8") as f:
                    return self.send_json({"note": f.read()})
            return self.send_json({"note": None}, 404)

        # 自定义阅读背景图
        if path == "/bg":
            bg = os.path.join(ROOT, "custom_bg.img")
            if not os.path.exists(bg):
                return self.send_json({"error": "not found"}, 404)
            with open(bg, "rb") as f:
                data = f.read()
            ctype = "image/jpeg"
            if data[:8] == b"\x89PNG\r\n\x1a\n":
                ctype = "image/png"
            elif data[:4] == b"GIF8":
                ctype = "image/gif"
            elif data[:4] == b"RIFF" and data[8:12] == b"WEBP":
                ctype = "image/webp"
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "max-age=86400")
            self.end_headers()
            self.wfile.write(data)
            return

        # Rhys 专用：列出所有还没回应的批注
        if path == "/api/pending":
            out = []
            for b in list_books():
                adir = os.path.join(BOOKS_DIR, b["slug"], "annotations")
                if not os.path.isdir(adir):
                    continue
                for fn in sorted(os.listdir(adir)):
                    for a in load_json(os.path.join(adir, fn), []):
                        if not a.get("replies"):
                            out.append({"book": b["slug"], "chapter": int(fn[:3]), **a})
            return self.send_json(out)

        self.send_json({"error": "not found"}, 404)

    def do_POST(self):
        path = unquote(urlparse(self.path).path)
        if not self.authed():
            return self.send_json({"error": "unauthorized"}, 401)

        if path == "/api/upload":
            raw = self.body()
            name = unquote(self.headers.get("X-Filename", "book.txt"))
            if not raw:
                return self.send_json({"ok": False, "error": "空文件"})
            try:
                slug, meta = save_book(name, raw)
            except Exception as e:
                return self.send_json({"ok": False, "error": str(e)})
            gen_notes_async(slug)
            return self.send_json({"ok": True, "slug": slug,
                                   "title": meta["title"], "count": len(meta["chapters"])})

        if path == "/api/delete":
            d = json.loads(self.body() or b"{}")
            slug = str(d.get("slug", ""))
            # 只认书架上真实存在的目录名，从根上堵掉 ../ 这类路径穿越
            if not slug or slug not in set(os.listdir(BOOKS_DIR) if os.path.isdir(BOOKS_DIR) else []):
                return self.send_json({"ok": False, "error": "没这本书"})
            bdir = os.path.join(BOOKS_DIR, slug)
            if not os.path.isdir(bdir):
                return self.send_json({"ok": False, "error": "没这本书"})
            title = load_json(os.path.join(bdir, "meta.json"), {}).get("title", slug)
            shutil.rmtree(bdir)
            prog = load_json(PROGRESS_FILE, {})
            if prog.pop(slug, None) is not None:
                save_json(PROGRESS_FILE, prog)
            return self.send_json({"ok": True, "title": title})

        if path == "/api/bg":
            raw = self.body()
            if not raw:
                return self.send_json({"ok": False, "error": "空文件"})
            if len(raw) > 8 * 1024 * 1024:
                return self.send_json({"ok": False, "error": "图片超过8MB"})
            with open(os.path.join(ROOT, "custom_bg.img"), "wb") as f:
                f.write(raw)
            return self.send_json({"ok": True})

        if path == "/api/progress":
            d = json.loads(self.body() or b"{}")
            prog = load_json(PROGRESS_FILE, {})
            prog[d["slug"]] = {"ch": d["ch"], "page": d["page"],
                               "mode": d["mode"], "ts": int(time.time())}
            save_json(PROGRESS_FILE, prog)
            return self.send_json({"ok": True})

        m = re.match(r"^/api/annotations/([^/]+)/(\d+)$", path)
        if m:
            slug, idx = m.group(1), int(m.group(2))
            d = json.loads(self.body() or b"{}")
            annos = load_json(anno_path(slug, idx), [])
            annos.append({
                "id": uuid.uuid4().hex[:8],
                "anchor": d.get("anchor", "")[:300],
                "note": d.get("note", "")[:2000],
                "who": "user",
                "ts": time.strftime("%Y-%m-%d %H:%M"),
                "replies": [],
            })
            save_json(anno_path(slug, idx), annos)
            return self.send_json({"ok": True})

        # Railway 分支改动：给 AI 回批注的接口。
        # 上游假定 AI 跟书住在同一台机器上，直接改 annotations/NNN.json；
        # 言住在另一台机器（tg 容器）上，够不着这边的磁盘，所以走 HTTP。
        # 只往 replies 里追加，她写的字一个都不动。
        m = re.match(r"^/api/reply/([^/]+)/(\d+)$", path)
        if m:
            slug, idx = m.group(1), int(m.group(2))
            d = json.loads(self.body() or b"{}")
            aid = str(d.get("id", "")).strip()
            text = str(d.get("text", "")).strip()[:4000]
            if not aid or not text:
                return self.send_json({"ok": False, "error": "缺 id 或 text"}, 400)
            ap = anno_path(slug, idx)
            annos = load_json(ap, [])
            for a in annos:
                if a.get("id") == aid:
                    a.setdefault("replies", []).append({
                        "who": "ai",
                        "text": text,
                        "ts": time.strftime("%Y-%m-%d %H:%M"),
                    })
                    save_json(ap, annos)
                    return self.send_json({"ok": True})
            return self.send_json({"ok": False, "error": "没有这条批注"}, 404)

        self.send_json({"error": "not found"}, 404)

    def do_DELETE(self):
        u = urlparse(self.path)
        path = unquote(u.path)
        qs = dict(p.split("=", 1) for p in u.query.split("&") if "=" in p)
        if not self.authed():
            return self.send_json({"error": "unauthorized"}, 401)
        m = re.match(r"^/api/annotations/([^/]+)/(\d+)$", path)
        if m:
            slug, idx = m.group(1), int(m.group(2))
            annos = load_json(anno_path(slug, idx), [])
            annos = [a for a in annos if a["id"] != qs.get("id")]
            save_json(anno_path(slug, idx), annos)
            return self.send_json({"ok": True})
        self.send_json({"error": "not found"}, 404)


if __name__ == "__main__":
    server = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    print(f"共读小屋 running on :{PORT}")
    server.serve_forever()
