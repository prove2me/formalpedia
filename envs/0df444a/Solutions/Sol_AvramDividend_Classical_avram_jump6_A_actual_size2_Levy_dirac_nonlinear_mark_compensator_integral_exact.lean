-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_size2_Levy_dirac_nonlinear_mark_compensator_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:19:29.848714+00:00
-- url     : https://prove2.me/submissions/f8662d13-a845-4632-91b4-c0228573eb0c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_overshoot_nonlinear_jump_correction_uniform_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory AvramDividend.Classical
noncomputable section
theorem solution
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z : ℝ,
        ((if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) - z)
      ∂(Measure.dirac (-2 : ℝ))) = 1 - y - y ^ 2 ∧
    (19 / 25 : ℝ) ≤
      ∫ z : ℝ,
        ((if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) - z)
      ∂(Measure.dirac (-2 : ℝ)) := by
  have hovershoot : y + (-2 : ℝ) < 0 := by linarith
  have hypos : ¬ y < (0 : ℝ) := not_lt_of_ge hy
  have hIntegral :
      (∫ z : ℝ,
        ((if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) - z)
        ∂(Measure.dirac (-2 : ℝ))) = 1 - y - y ^ 2 := by
    rw [integral_dirac]
    simp only [if_pos hovershoot, if_neg hypos]
    ring
  constructor
  · exact hIntegral
  · rw [hIntegral]
    nlinarith [sq_nonneg (y - 1 / 5)]
