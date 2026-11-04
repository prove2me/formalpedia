-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_jump_drift_eq_generator_sub_physical_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:40:20.389261+00:00
-- url     : https://prove2.me/submissions/43c32b4a-1fa3-4867-b67a-4ef8aa7970ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original BV Lévy jump-compensator drift is the source
generator, with its exact truncation convention, minus the physical BV drift. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (u : ℝ) (hGen : X.GeneratorIntegrable w u) :
    (∫ z in Iio (0 : ℝ), w (u + z) - w u ∂X.ν) =
      X.generator w u - X.drift * deriv w u := by
  have hrepr :=
    boundedVariation_generator_physical_drift_representation
      X hBV w u hGen
  linarith
