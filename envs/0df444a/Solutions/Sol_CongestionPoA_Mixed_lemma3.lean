-- Prove2me | solution 1 for CongestionPoA.Mixed.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:57:20.090251+00:00
-- url     : https://prove2.me/submissions/5cdd345c-db79-4bdc-9b99-3d5e7dab5cfc

import Mathlib

theorem solution (x : ℝ) (hx : 0 ≤ x) (y : ℕ) :
    (y : ℝ) * (x + 1) ≤ (Real.sqrt 5 - 1) / 4 * x ^ 2 + (Real.sqrt 5 + 5) / 4 * (y : ℝ) ^ 2 := by
  set s := Real.sqrt 5 with hsdef
  have hs : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : 2 < s := by
    rw [hsdef, show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hyy : 0 ≤ (y : ℝ) * ((y : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos y with h | h
    · subst h; simp
    · have : (1 : ℝ) ≤ y := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  have key : (s - 1) * ((s - 1) / 4 * x ^ 2 + (s + 5) / 4 * (y : ℝ) ^ 2 - (y : ℝ) * (x + 1))
      = ((s - 1) / 2 * x - y) ^ 2 + (s - 1) * ((y : ℝ) * ((y : ℝ) - 1)) := by
    linear_combination ((y : ℝ) ^ 2 / 4) * hs
  have hpos : 0 < s - 1 := by linarith
  have h1 : 0 ≤ (s - 1) * ((s - 1) / 4 * x ^ 2 + (s + 5) / 4 * (y : ℝ) ^ 2 - (y : ℝ) * (x + 1)) := by
    rw [key]; exact add_nonneg (sq_nonneg _) (mul_nonneg hpos.le hyy)
  have h2 := (mul_nonneg_iff_of_pos_left hpos).mp h1
  linarith
