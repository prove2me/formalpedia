-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_uniform_negative_smallmark_quadratic_energy_one_third
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:12:33.691312+00:00
-- url     : https://prove2.me/submissions/56cd68dc-89a5-4a18-b503-2dea5a1d740b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal Topology
noncomputable section

/-- Uniform negative marks carry strictly positive quadratic energy. -/
theorem solution :
    (∫ z in Ioo (-1 : ℝ) 0, z ^ 2
      ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) =
      (1 / 3 : ℝ) := by
  have hset :
      (∫ z in Ioo (-1 : ℝ) 0, z ^ 2
        ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) =
      (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂(volume : Measure ℝ)) := by
    simp [Measure.restrict_restrict, Set.inter_self]
  rw [hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
  norm_num [integral_pow]
