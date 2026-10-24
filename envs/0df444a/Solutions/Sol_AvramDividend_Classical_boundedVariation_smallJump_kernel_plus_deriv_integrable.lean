-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_smallJump_kernel_plus_deriv_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:07:51.544949+00:00
-- url     : https://prove2.me/submissions/01752f00-d619-4592-a068-7b8afb6ec94c

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Recover integrability of the full BV small-jump increment kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn
      (fun y : ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand w x y + deriv w x * y)
      (Ioo (-1 : ℝ) 0) X.ν := by
  have hsub : Ioo (-1 : ℝ) 0 ⊆ Iio 0 := by
    intro y hy
    exact hy.2
  exact (hGen.mono_set hsub).add
    (boundedVariation_smallJump_deriv_integrable X hBV w x)
