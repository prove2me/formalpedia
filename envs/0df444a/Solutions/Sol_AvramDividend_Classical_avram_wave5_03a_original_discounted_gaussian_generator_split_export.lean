-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_original_discounted_gaussian_generator_split_export
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:45:02.228858+00:00
-- url     : https://prove2.me/submissions/66f0c9a4-6cf1-454a-ade0-e185a57c1553

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact discounted source generator split, independent of a Gaussian hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q t y : ℝ) :
    Real.exp (-(q * t)) * (X.generator w y - q * w y) =
      Real.exp (-(q * t)) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w y) +
        Real.exp (-(q * t)) *
          (X.c * deriv w y +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
                q * w y) := by
  change
    Real.exp (-(q * t)) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
        X.c * deriv w y +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
              q * w y) =
      Real.exp (-(q * t)) * (X.σ ^ 2 / 2 * iteratedDeriv 2 w y) +
        Real.exp (-(q * t)) *
          (X.c * deriv w y +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
                q * w y)
  ring