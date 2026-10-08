-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_contDiff_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:39:54.781289+00:00
-- url     : https://prove2.me/submissions/9ec4622b-74d8-4409-acff-b67d3a561aed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    X.GeneratorIntegrable W x := by
  obtain ⟨C, hC, hbound⟩ :=
    scaleFunction_generatorIntegrand_min_sq_bound_of_contDiff_two
      X q W hW a x hx hC2
  apply generatorIntegrable_of_min_sq_bound X W x C hC
  · exact scaleFunction_generatorIntegrand_aestronglyMeasurable X q W hW x
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Iio] with y hy
    exact hbound y hy
