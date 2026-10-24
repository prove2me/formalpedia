-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_generator_eq_drift_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:45:58.470679+00:00
-- url     : https://prove2.me/submissions/4cb5a303-4485-4708-a872-9306a486f043

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The Gaussian second-derivative term of the Lévy generator vanishes
    identically for bounded-variation Lévy paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) :
    X.generator w x =
      X.c * deriv w x +
        ∫ y in Iio (0 : ℝ),
          (w (x + y) - w x -
            deriv w x * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν := by
  have hσ : X.σ = 0 := hBV.1
  simp [SpectrallyNegativeLevy.generator,
    SpectrallyNegativeLevy.generatorIntegrand, hσ]
