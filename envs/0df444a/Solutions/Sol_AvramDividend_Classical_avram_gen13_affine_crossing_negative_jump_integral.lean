-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen13_affine_crossing_negative_jump_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:27:52.80272+00:00
-- url     : https://prove2.me/submissions/dd541864-f652-4f41-aaa4-7ebeefe9807d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen13_affine_kernel_negative_jump_substitution
import Theorems.Thm_AvramDividend_Classical_avram_gen13_affine_kernel_density_interval_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The affine ruin-crossing negative-jump power integral has an exact value. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ z in (-1 : ℝ)..(-y), (-1 - y - z) *
      |z| ^ (-(3 / 2 : ℝ))) =
      2 * (1 - y ^ (1 / 2 : ℝ)) -
      (1 + y) * (2 * (y ^ (-(1 / 2 : ℝ)) - 1)) := by
  rw [AvramDividend.Classical.avram_gen13_affine_kernel_negative_jump_substitution y hy hy1]
  exact AvramDividend.Classical.avram_gen13_affine_kernel_density_interval_integral y hy hy1
