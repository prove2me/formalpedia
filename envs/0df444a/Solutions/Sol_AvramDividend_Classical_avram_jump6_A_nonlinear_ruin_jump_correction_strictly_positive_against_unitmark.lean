-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:25:57.486272+00:00
-- url     : https://prove2.me/submissions/782ec47a-3bf8-4cd7-bca5-8a0a7f95993f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 ≤ y) (hycap : y ≤ 1 / 5) :
    (if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
      (if y < 0 then 0 else 1 + y + y ^ 2) - (-2 : ℝ) ≥ 19 / 25 := by
  have hminus : y - 2 < (0 : ℝ) := by linarith
  have hpos : ¬ y < (0 : ℝ) := not_lt_of_ge hy
  simp only [if_pos hminus, if_neg hpos]
  have hsq : y ^ 2 ≤ (1 / 25 : ℝ) := by nlinarith [sq_nonneg (y - 1 / 5)]
  nlinarith
