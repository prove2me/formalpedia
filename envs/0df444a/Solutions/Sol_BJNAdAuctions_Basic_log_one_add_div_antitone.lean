-- Prove2me | solution 1 for BJNAdAuctions.Basic.log_one_add_div_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:19:15.181992+00:00
-- url     : https://prove2.me/submissions/b0606156-cd5a-498a-913d-6942a35b5727

import Mathlib

open Real in
theorem solution (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    Real.log (1 + y) / y ≤ Real.log (1 + x) / x := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have ha : 0 ≤ 1 - x / y := by
    rw [sub_nonneg, div_le_one hy0]; exact hxy
  have hb : 0 ≤ x / y := div_nonneg hx.le hy0.le
  have hab : (1 - x / y) + x / y = 1 := by ring
  have h1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have h2 : (1 + y) ∈ Set.Ioi (0:ℝ) := by
    show (0:ℝ) < 1 + y; linarith
  have key := (strictConcaveOn_log_Ioi).concaveOn.2 h1 h2 ha hb hab
  have hpt : (1 - x / y) • (1:ℝ) + (x / y) • (1 + y) = 1 + x := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hpt] at key
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at key
  -- key : x / y * log (1 + y) ≤ log (1 + x)
  rw [div_le_div_iff₀ hy0 hx]
  have : x / y * Real.log (1 + y) * y = x * Real.log (1 + y) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_right key hy0.le]
