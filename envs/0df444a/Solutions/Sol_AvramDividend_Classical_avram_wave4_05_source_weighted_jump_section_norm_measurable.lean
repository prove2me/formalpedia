-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_weighted_jump_section_norm_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:04:43.633584+00:00
-- url     : https://prove2.me/submissions/53cef170-ca7b-4253-8094-dc8783a03af0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The jump-indexed weighted x-section norm is measurable on the original
    negative-jump Levy measure, even before product integrability is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (θ : ℝ) :
    AEStronglyMeasurable
      (fun y : ℝ => ∫ x in Ioi (0 : ℝ),
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖)
      (X.ν.restrict (Iio (0 : ℝ))) := by
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
  have hm : Measurable
      (fun p : ℝ × ℝ => ‖Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2‖) := by
    fun_prop
  have hs : StronglyMeasurable
      (fun y : ℝ => ∫ x,
        ‖Real.exp (-(θ * x)) *
          SpectrallyNegativeLevy.generatorIntegrand W x y‖
        ∂(volume.restrict (Ioi (0 : ℝ)))) := by
    exact StronglyMeasurable.integral_prod_left
      (μ := volume.restrict (Ioi (0 : ℝ))) hm.stronglyMeasurable
  exact hs.aestronglyMeasurable
