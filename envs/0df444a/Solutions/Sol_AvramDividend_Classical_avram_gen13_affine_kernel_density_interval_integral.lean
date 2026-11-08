-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen13_affine_kernel_density_interval_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:20:36.270504+00:00
-- url     : https://prove2.me/submissions/72e205b3-20cb-40a6-9a7d-94fa590ee440

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen12_singular_power_tail_integral
import Theorems.Thm_AvramDividend_Classical_avram_gen12_singular_half_power_tail_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Integrate the singular affine crossing kernel in positive jump-magnitude coordinates. -/
theorem solution
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ r in y..1, (r ^ (-(1 / 2 : ℝ)) -
      (1 + y) * r ^ (-(3 / 2 : ℝ)))) =
      2 * (1 - y ^ (1 / 2 : ℝ)) -
      (1 + y) * (2 * (y ^ (-(1 / 2 : ℝ)) - 1)) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc y 1 := by
    rw [Set.uIcc_of_le hy1]
    exact fun hz => (not_le.mpr hy) hz.1
  have hf : IntervalIntegrable (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) volume y 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hg0 : IntervalIntegrable (fun r : ℝ => r ^ (-(3 / 2 : ℝ))) volume y 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hg : IntervalIntegrable
      (fun r : ℝ => (1 + y) * r ^ (-(3 / 2 : ℝ))) volume y 1 :=
    hg0.const_mul (1 + y)
  rw [intervalIntegral.integral_sub hf hg, intervalIntegral.integral_const_mul]
  rw [AvramDividend.Classical.avram_gen12_singular_half_power_tail_integral y hy hy1]
  rw [AvramDividend.Classical.avram_gen12_singular_power_tail_integral y hy hy1]
