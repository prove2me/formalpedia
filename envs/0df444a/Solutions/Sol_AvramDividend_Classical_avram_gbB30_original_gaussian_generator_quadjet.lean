-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_original_gaussian_generator_quadjet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:38:05.586204+00:00
-- url     : https://prove2.me/submissions/0c778381-7091-4036-8fc0-c1659b822f5b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (0 : Measure ℝ)) (hσ : X.σ = 1) (hc : X.c = 2)
    (w : ℝ → ℝ) (y : ℝ)
    (hw0 : w y = 2 * y - 4 * y ^ 2)
    (hw1 : deriv w y = 2 - 8 * y)
    (hw2 : iteratedDeriv 2 w y = -8) :
    X.GeneratorIntegrable w y ∧
      X.generator w y - (1 / 100 : ℝ) * w y =
        (1 / 25 : ℝ) * y ^ 2 - (1602 / 100 : ℝ) * y := by 
  have hInt : X.GeneratorIntegrable w y := by
    simpa [SpectrallyNegativeLevy.GeneratorIntegrable, IntegrableOn, hν] using
      (integrable_zero_measure : Integrable
        (generatorIntegrand w y) (0 : Measure ℝ))
  refine ⟨hInt, ?_⟩
  simp [SpectrallyNegativeLevy.generator, hν, hσ, hc, hw0, hw1, hw2]
  ring
