-- Prove2me | solution 1 for CodedSorting.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-10T10:58:25.842277+00:00
-- url     : https://prove2.me/submissions/d1e8019c-35c4-4d4e-98ad-c16fd7a43f52

import Mathlib

theorem solution : (3 : ℝ) / 200000 * Real.log 512 < 33 / 338432 := by
  have h : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h]
  linarith [Real.log_two_lt_d9]
