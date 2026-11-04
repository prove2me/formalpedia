-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_discounted_HJB_source_jump_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:11:51.309263+00:00
-- url     : https://prove2.me/submissions/75f6b3ac-b7c7-41e4-b023-d62b9f758731

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discounted original BV HJB residual has the sign required for the
expected signed-cash inequality at a genuine source pre-payment state. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (u q t : ℝ) (hGen : X.GeneratorIntegrable w u)
    (hHJB : X.generator w u - q * w u ≤ 0) :
    Real.exp (-(q * t)) *
      (X.drift * deriv w u +
        (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) -
        q * w u) ≤ 0 := by
  have hrepr :=
    boundedVariation_generator_physical_drift_representation
      X hBV w u hGen
  have hcore : X.drift * deriv w u +
      (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) -
      q * w u ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos (-(q * t)))) hcore
