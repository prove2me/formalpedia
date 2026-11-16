-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_weak_HJB_positive_reserve_drift_negative_mark_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:00:43.989146+00:00
-- url     : https://prove2.me/submissions/d5d859c3-d6d3-4986-9a79-959fedb10089

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.drift +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by
  have hd : 0 ≤ X.drift :=
    (bv_standing_drift_pos X hStanding hBV).1.le
  have hInt := (hGen y hy hyC).1
  have hSign := (hGen y hy hyC).2
  rw [boundedVariation_generator_physical_drift_representation
      X hBV w y hInt] at hSign
  have hGrad' : 0 ≤ deriv w y - 1 := sub_nonneg.mpr (hGrad y hy hyC)
  nlinarith [mul_nonneg hd hGrad']
