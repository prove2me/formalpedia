-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_smooth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T20:59:45.705984+00:00
-- url     : https://prove2.me/submissions/fb6eff6d-ea1a-4306-adc9-43d30fe59317
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_levyMeasure_absolutelyContinuous_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by
  intro x hx
  rcases h_smooth with hσ | hs
  · have hC2all :=
      scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
    exact scaleFunction_generatorIntegrable_of_contDiff_two
      X q W hW a x hx (hC2all.mono fun z hz => hz.1)
  · rcases hs with hbv | hC2
    · have hac :=
        levyMeasure_absolutelyContinuous_of_standing_boundedVariation
          X hX hbv
      have hC1 :=
        scaleFunction_contDiff_one_of_absolutely_continuous_levy
          X hX q hq W hW hac
      exact scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
        X q W hW hbv x hx.1 hC1
    · exact scaleFunction_generatorIntegrable_of_contDiff_two
        X q W hW a x hx hC2
