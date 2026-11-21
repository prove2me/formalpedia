-- Prove2me | solution 1 for BehrendWindows.small_range_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:59:30.308974+00:00
-- url     : https://prove2.me/submissions/d4538ec0-84e8-4520-b281-aeb8350768ef

import Mathlib

theorem solution (C : ℝ) (hC : 0 < C) (N m : ℕ) (hN : 1 ≤ N)
    (hNm : (N : ℝ) ≤ (m : ℝ) ^ (C ^ 2)) :
    (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log N * Real.log m)) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- `m ≥ 1`, since `0 ^ (C ^ 2) = 0`
  have hm : (0 : ℝ) < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [Nat.cast_zero, Real.zero_rpow (by positivity)] at hNm
      linarith
    · exact_mod_cast h
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 < m := by exact_mod_cast hm
    exact_mod_cast this
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hl : 0 ≤ Real.log m := Real.log_nonneg hm1
  -- `log N ≤ C² log m`
  have hlog : Real.log N ≤ C ^ 2 * Real.log m := by
    have := Real.log_le_log hN0 hNm
    rwa [Real.log_rpow hm] at this
  -- `log N ≤ C √(log N log m)`
  have hkey : Real.log N ≤ C * Real.sqrt (Real.log N * Real.log m) := by
    have h1 : Real.log N ≤ Real.sqrt (C ^ 2 * (Real.log N * Real.log m)) := by
      rw [Real.le_sqrt hL (by positivity)]
      nlinarith
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hC.le] at h1
  calc (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log N * Real.log m))
      ≤ N * Real.exp (-Real.log N) := by
        gcongr
        linarith
    _ = 1 := by
        rw [Real.exp_neg, Real.exp_log hN0]
        field_simp
