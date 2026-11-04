-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_HJB_physical_drift_plus_jump_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:08:05.315097+00:00
-- url     : https://prove2.me/submissions/d4bb5347-7bf5-46fa-96db-e7aa9ccc48f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV generator HJB bound is exactly the combined physical
drift and original jump-compensator bound used at a pre-dividend source state. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (u q : ℝ) (hGen : X.GeneratorIntegrable w u)
    (hHJB : X.generator w u - q * w u ≤ 0) :
    X.drift * deriv w u +
        (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) -
        q * w u ≤ 0 := by
  have hrepr :=
    boundedVariation_generator_physical_drift_representation
      X hBV w u hGen
  linarith
