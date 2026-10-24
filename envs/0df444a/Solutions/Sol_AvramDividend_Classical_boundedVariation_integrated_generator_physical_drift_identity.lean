-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_integrated_generator_physical_drift_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:53:29.580211+00:00
-- url     : https://prove2.me/submissions/dabb7117-48a2-45c5-88f7-01b0f67e5107

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The BV generator's uncompensated negative-jump representation can be
    substituted pointwise beneath any discounted restricted integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (μ : Measure ℝ) (u : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (hGen : ∀ t ∈ A, X.GeneratorIntegrable w (u t)) :
    (∫ t in A, Real.exp (-(q * t)) *
      (X.generator w (u t) - q * w (u t)) ∂μ) =
      ∫ t in A, Real.exp (-(q * t)) *
        (X.drift * deriv w (u t) +
          (∫ y in Iio (0 : ℝ), w (u t + y) - w (u t) ∂X.ν) -
          q * w (u t)) ∂μ := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
  rw [boundedVariation_generator_physical_drift_representation
    X hBV w (u t) (hGen t ht)]
