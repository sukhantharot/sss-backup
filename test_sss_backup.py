#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ชุดทดสอบ sss_backup.py

    python -m pytest test_sss_backup.py -v
    หรือรันตรงๆ:  python test_sss_backup.py
"""

import os
import sys
import shutil
import hashlib
import tempfile
import itertools
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sss_backup as S


# =====================================================================
#  1) เลขคณิต GF(256)
# =====================================================================

class TestGaloisField(unittest.TestCase):
    """บั๊กในชั้นนี้จะไม่ทำให้โปรแกรม error — มันจะเงียบแล้วกู้ไฟล์ไม่ได้
    เพราะฉะนั้นต้องทดสอบให้ครบทุกคู่"""

    @staticmethod
    def _ref_mul(a, b):
        """คูณแบบ shift-and-add ไว้เทียบกับผลจากตาราง log/exp"""
        p = 0
        while b:
            if b & 1:
                p ^= a
            a = S._xtime(a)
            b >>= 1
        return p

    def test_known_value(self):
        # (x+1)(x²+x+1) = x³+1  ->  3 · 7 = 9
        # ถ้าตารางใช้ตัวสร้างผิด (2 แทน 3) ข้อนี้จะพัง
        self.assertEqual(S.gf_mul(3, 7), 9)

    def test_all_products(self):
        for a in range(256):
            for b in range(256):
                self.assertEqual(S.gf_mul(a, b), self._ref_mul(a, b),
                                 f"gf_mul({a},{b}) ผิด")

    def test_generator_covers_field(self):
        """ตัวสร้างต้องวนครบ 255 ตัวที่ไม่ใช่ศูนย์"""
        self.assertEqual(len(set(S.GF_EXP[:255])), 255)

    def test_inverse(self):
        for a in range(1, 256):
            self.assertEqual(S.gf_mul(a, S.gf_inv(a)), 1)

    def test_inverse_of_zero_raises(self):
        with self.assertRaises(ZeroDivisionError):
            S.gf_inv(0)

    def test_mul_table_matches(self):
        for c in (0, 1, 3, 17, 200, 255):
            for v in range(256):
                self.assertEqual(S.MUL_TABLE[c][v], S.gf_mul(v, c))


# =====================================================================
#  2) Shamir's Secret Sharing
# =====================================================================

class TestSecretSharing(unittest.TestCase):

    def test_every_combination_recovers(self):
        """ทุกชุดผสม k จาก n ต้องกู้ได้เหมือนกันหมด"""
        data = os.urandom(256)
        for k, n in [(2, 3), (3, 5), (4, 6)]:
            shares = S.sss_split(data, k, n)
            for combo in itertools.combinations(range(1, n + 1), k):
                got = S.sss_combine({x: shares[x] for x in combo})
                self.assertEqual(got, data, f"k={k} n={n} combo={combo}")

    def test_extra_shares_still_work(self):
        """ให้ share เกิน k ก็ต้องได้ผลเดิม"""
        data = os.urandom(128)
        shares = S.sss_split(data, 3, 5)
        self.assertEqual(S.sss_combine(shares), data)

    def test_insufficient_shares_reveal_nothing(self):
        data = os.urandom(128)
        shares = S.sss_split(data, 3, 5)
        self.assertNotEqual(S.sss_combine({1: shares[1], 2: shares[2]}), data)

    def test_share_is_not_plaintext(self):
        """share ต้องไม่มีร่องรอยของข้อมูลเดิม"""
        data = b'A' * 512
        for sh in S.sss_split(data, 3, 5).values():
            self.assertNotIn(b'AAAAAAAA', sh)

    def test_size_preserved(self):
        for size in (0, 1, 15, 1000):
            data = os.urandom(size)
            for sh in S.sss_split(data, 3, 5).values():
                self.assertEqual(len(sh), size)

    def test_randomness_differs_between_runs(self):
        """แตกไฟล์เดิมสองครั้งต้องได้ share คนละชุด"""
        data = os.urandom(64)
        self.assertNotEqual(S.sss_split(data, 3, 5)[1],
                            S.sss_split(data, 3, 5)[1])

    def test_invalid_params(self):
        for k, n in [(1, 5), (5, 3), (3, 256)]:
            with self.assertRaises(ValueError):
                S.sss_split(b'x' * 8, k, n)


# =====================================================================
#  3) ชั้นเข้ารหัส
# =====================================================================

class TestCrypto(unittest.TestCase):

    def test_roundtrip(self):
        salt, nonce = os.urandom(16), os.urandom(16)
        ke, km = S.derive_keys('รหัสผ่านภาษาไทย', salt)
        plain = os.urandom(1000)
        ct, tag = S.encrypt(plain, ke, km, nonce)
        self.assertNotEqual(ct, plain)
        self.assertEqual(S.decrypt(ct, tag, ke, km, nonce), plain)

    def test_wrong_password_rejected(self):
        salt, nonce = os.urandom(16), os.urandom(16)
        ke, km = S.derive_keys('ถูก', salt)
        ct, tag = S.encrypt(b'secret data', ke, km, nonce)
        ke2, km2 = S.derive_keys('ผิด', salt)
        with self.assertRaises(ValueError):
            S.decrypt(ct, tag, ke2, km2, nonce)

    def test_tampered_ciphertext_rejected(self):
        salt, nonce = os.urandom(16), os.urandom(16)
        ke, km = S.derive_keys('pw', salt)
        ct, tag = S.encrypt(b'x' * 100, ke, km, nonce)
        bad = bytearray(ct)
        bad[50] ^= 1
        with self.assertRaises(ValueError):
            S.decrypt(bytes(bad), tag, ke, km, nonce)

    def test_salt_changes_key(self):
        a = S.derive_keys('pw', b'\x00' * 16)
        b = S.derive_keys('pw', b'\x01' * 16)
        self.assertNotEqual(a, b)


# =====================================================================
#  4) ทดสอบทั้งระบบ (end-to-end)
# =====================================================================

class TestEndToEnd(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.src = os.path.join(self.tmp, 'PQC.md')
        self.data = os.urandom(92_927)
        with open(self.src, 'wb') as f:
            f.write(self.data)
        self.digest = hashlib.sha256(self.data).hexdigest()

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _sha(self, path):
        with open(path, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest()

    def test_split_then_restore_after_losing_two(self):
        """สถานการณ์จริง: share หาย 2 ชิ้น ไฟล์ต้นฉบับก็หาย"""
        S.do_split(self.src, 'pw123', k=3, n=5)
        os.remove(os.path.join(self.tmp, 'part1.bin'))
        os.remove(os.path.join(self.tmp, 'part4.bin'))
        os.remove(self.src)

        dest, meta = S.do_restore(self.tmp, 'pw123')
        self.assertEqual(meta['name'], 'PQC.md')
        self.assertEqual(meta['size'], 92_927)
        self.assertEqual(self._sha(dest), self.digest)

    def test_restore_works_without_manifest(self):
        """manifest.json ต้องไม่จำเป็นต่อการกู้คืน"""
        S.do_split(self.src, 'pw', k=3, n=5)
        os.remove(os.path.join(self.tmp, 'manifest.json'))
        os.remove(self.src)
        dest, _ = S.do_restore(self.tmp, 'pw')
        self.assertEqual(self._sha(dest), self.digest)

    def test_share_does_not_leak_filename(self):
        """ชื่อไฟล์เดิมกับ hash ต้องถูกซ่อนอยู่ในส่วนที่เข้ารหัส"""
        S.do_split(self.src, 'pw', k=3, n=5)
        with open(os.path.join(self.tmp, 'part1.bin'), 'rb') as f:
            raw = f.read()
        self.assertNotIn(b'PQC.md', raw)
        self.assertNotIn(self.digest.encode(), raw)

    def test_wrong_password_on_restore(self):
        S.do_split(self.src, 'correct', k=3, n=5)
        os.remove(self.src)
        with self.assertRaises(ValueError):
            S.do_restore(self.tmp, 'wrong')

    def test_too_few_shares(self):
        S.do_split(self.src, 'pw', k=3, n=5)
        for i in (1, 2, 4):
            os.remove(os.path.join(self.tmp, f'part{i}.bin'))
        with self.assertRaises(SystemExit):
            S.do_restore(self.tmp, 'pw')

    def test_ignores_unrelated_bin_files(self):
        S.do_split(self.src, 'pw', k=3, n=5)
        with open(os.path.join(self.tmp, 'garbage.bin'), 'wb') as f:
            f.write(os.urandom(500))
        os.remove(self.src)
        dest, _ = S.do_restore(self.tmp, 'pw')
        self.assertEqual(self._sha(dest), self.digest)

    def test_two_backup_sets_in_same_folder(self):
        """มี backup สองชุดปนกัน ต้องเลือกชุดที่สมบูรณ์กว่า"""
        other = os.path.join(self.tmp, 'other.txt')
        with open(other, 'wb') as f:
            f.write(b'different file')
        S.do_split(other, 'pw', k=2, n=2, outdir=os.path.join(self.tmp, 'a'))
        S.do_split(self.src, 'pw', k=3, n=5)
        for name in os.listdir(os.path.join(self.tmp, 'a')):
            if name.endswith('.bin'):
                shutil.copy(os.path.join(self.tmp, 'a', name),
                            os.path.join(self.tmp, 'x_' + name))
        os.remove(self.src)
        dest, meta = S.do_restore(self.tmp, 'pw')
        self.assertEqual(meta['name'], 'PQC.md')

    def test_empty_file(self):
        empty = os.path.join(self.tmp, 'empty.txt')
        open(empty, 'wb').close()
        S.do_split(empty, 'pw', k=3, n=5, outdir=os.path.join(self.tmp, 'e'))
        os.remove(empty)
        dest, meta = S.do_restore(os.path.join(self.tmp, 'e'), 'pw',
                                  outdir=os.path.join(self.tmp, 'e'))
        self.assertEqual(meta['size'], 0)

    def test_binary_and_unicode_filename(self):
        name = os.path.join(self.tmp, 'เอกสารลับ.pdf')
        payload = bytes(range(256)) * 40
        with open(name, 'wb') as f:
            f.write(payload)
        d = os.path.join(self.tmp, 'u')
        S.do_split(name, 'รหัส', k=2, n=3, outdir=d)
        os.remove(name)
        dest, meta = S.do_restore(d, 'รหัส', outdir=d)
        self.assertEqual(meta['name'], 'เอกสารลับ.pdf')
        with open(dest, 'rb') as f:
            self.assertEqual(f.read(), payload)

    def test_header_format_size(self):
        self.assertEqual(S.HDR_LEN, 78)
        S.do_split(self.src, 'pw', k=3, n=5)
        size = os.path.getsize(os.path.join(self.tmp, 'part1.bin'))
        self.assertEqual(size, 92_927 + S.HDR_LEN + 2 + len(
            __import__('json').dumps(
                {'name': 'PQC.md', 'size': 92927, 'sha256': self.digest},
                ensure_ascii=False).encode()))


# =====================================================================
#  5) การแสดงผลบนเทอร์มินัลที่ไม่รองรับ UTF-8
# ---------------------------------------------------------------------
#  เคสจริงที่เคยทำ CI พังบน windows-latest:
#  stdout ถูก redirect เข้า pipe -> Python ใช้ cp1252 -> print ไทยแล้วพัง
# =====================================================================

class TestNonUtf8Terminal(unittest.TestCase):

    def test_streams_are_utf8(self):
        """_force_utf8_output ต้องตั้ง encoding ได้จริง"""
        if hasattr(sys.stdout, 'encoding') and hasattr(sys.stdout, 'reconfigure'):
            self.assertEqual((sys.stdout.encoding or '').lower().replace('-', ''),
                             'utf8')

    def test_restore_prints_on_cp1252_stream(self):
        """เขียนข้อความของ do_restore ลง stream แบบ cp1252 ต้องไม่ throw"""
        import io
        tmp = tempfile.mkdtemp()
        try:
            src = os.path.join(tmp, 'ทดสอบ.txt')
            with open(src, 'wb') as f:
                f.write(os.urandom(2048))
            S.do_split(src, 'pw', k=3, n=5)
            os.remove(src)

            raw = io.BytesIO()
            fake = io.TextIOWrapper(raw, encoding='cp1252', errors='strict')
            real = sys.stdout
            sys.stdout = fake
            try:
                S.do_restore(tmp, 'pw')   # เดิมพังตรงนี้ด้วย UnicodeEncodeError
                fake.flush()
            finally:
                sys.stdout = real
        finally:
            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == '__main__':
    unittest.main(verbosity=2)
