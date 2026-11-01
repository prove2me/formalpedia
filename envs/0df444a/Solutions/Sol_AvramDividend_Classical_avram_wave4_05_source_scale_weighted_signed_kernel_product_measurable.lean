-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:59:25.790415+00:00
-- url     : https://prove2.me/submissions/5b535cf2-cd60-4d45-85e1-87ded91e63a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Signed, weighted source compensated Levy kernel jointly measurable
    on the exact positive-reserve x negative-jump product measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (θ : ℝ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by
  have hscale : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hd : Measurable (deriv W) := measurable_deriv W
  have hind : Measurable
      (fun y : ℝ => (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hker : Measurable
      (fun p : ℝ × ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    fun_prop
  have hweighted : Measurable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2) := by
    fun_prop
  exact hweighted.aestronglyMeasurable
