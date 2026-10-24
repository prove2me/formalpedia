-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_smallJump_generatorIntegral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:26:39.388828+00:00
-- url     : https://prove2.me/submissions/4dbdb682-bb3c-448b-b5f0-604dd241af3a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_small_negative
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_uncompensated_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Split the BV small-jump generator integral into increment and compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (∫ y in Ioo (-1 : ℝ) 0, SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) =
      (∫ y in Ioo (-1 : ℝ) 0, w (x + y) - w x ∂X.ν) -
      (∫ y in Ioo (-1 : ℝ) 0, deriv w x * y ∂X.ν) := by
  have hf :=
    boundedVariation_smallJump_uncompensated_integrable X hBV w x hGen
  have hg := boundedVariation_smallJump_deriv_integrable X hBV w x
  calc
    (∫ y in Ioo (-1 : ℝ) 0, SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) =
      ∫ y in Ioo (-1 : ℝ) 0,
        (w (x + y) - w x) - deriv w x * y ∂X.ν := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          intro y hy
          change SpectrallyNegativeLevy.generatorIntegrand w x y =
            (w (x + y) - w x) - deriv w x * y
          rw [generatorIntegrand_small_negative w x y hy]
    _ = _ := MeasureTheory.integral_sub hf hg
