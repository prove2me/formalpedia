-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_large_negative_overshoot_nonlinear_jump_correction_uniform_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:10:25.52983+00:00
-- url     : https://prove2.me/submissions/bedd3959-6c36-4674-9cf5-e16bb272337d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
noncomputable section
theorem solution
    (y z : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5)
    (hz : z ≤ -2) :
    (if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
      (if y < 0 then 0 else 1 + y + y ^ 2) - z ≥ 19 / 25 := by
  have hovershoot : y + z < (0 : ℝ) := by linarith
  have hypos : ¬ y < (0 : ℝ) := not_lt_of_ge hy
  simp only [if_pos hovershoot, if_neg hypos]
  have hsq : y ^ 2 ≤ (1 / 25 : ℝ) := by
    nlinarith [sq_nonneg (y - 1 / 5)]
  nlinarith
