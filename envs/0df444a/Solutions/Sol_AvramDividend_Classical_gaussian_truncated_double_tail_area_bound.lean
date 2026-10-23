-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_truncated_double_tail_area_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:07:26.320666+00:00
-- url     : https://prove2.me/submissions/5b5260a4-4204-477a-88bb-3e814da57cf8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (R z : ℝ) (hR : 0 ≤ R) (hz : 0 ≤ z) :
    0 ≤ z * min R z - (min R z) ^ 2 / 2 ∧
    z * min R z - (min R z) ^ 2 / 2 ≤
      (1 + R) * min (z ^ 2) z := by
  let u : ℝ := min R z
  have hu0 : 0 ≤ u := le_min hR hz
  have huz : u ≤ z := min_le_right R z
  have huR : u ≤ R := min_le_left R z
  have hupper : 0 ≤ z * u - u ^ 2 / 2 := by
    have hp : u * u ≤ z * u := mul_le_mul_of_nonneg_right huz hu0
    nlinarith
  constructor
  · exact hupper
  · by_cases hz1 : z ≤ 1
    · have hsq : z ^ 2 ≤ z := by
        nlinarith [mul_nonneg hz (sub_nonneg.mpr hz1)]
      rw [min_eq_left hsq]
      have hp : z * u ≤ z * z := mul_le_mul_of_nonneg_left huz hz
      have hRz : 0 ≤ R * z ^ 2 := mul_nonneg hR (sq_nonneg z)
      change z * u - u ^ 2 / 2 ≤ (1 + R) * z ^ 2
      nlinarith [sq_nonneg u]
    · have h1 : 1 ≤ z := le_of_lt (lt_of_not_ge hz1)
      have hsq : z ≤ z ^ 2 := by
        nlinarith [mul_nonneg hz (sub_nonneg.mpr h1)]
      rw [min_eq_right hsq]
      have hp : z * u ≤ z * R := mul_le_mul_of_nonneg_left huR hz
      change z * u - u ^ 2 / 2 ≤ (1 + R) * z
      nlinarith [sq_nonneg u]
