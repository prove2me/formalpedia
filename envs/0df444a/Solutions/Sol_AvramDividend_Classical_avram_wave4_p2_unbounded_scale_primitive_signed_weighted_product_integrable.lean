-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:02:53.230326+00:00
-- url     : https://prove2.me/submissions/35f70701-6ecb-4d1f-85ae-13c04b4e747d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_source_scale_primitive_global_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_weighted_jump_product_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Signed genuine source primitive kernel is absolutely product L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let f : ℝ × ℝ → ℝ := fun p => Real.exp (-(θ * p.1)) *
    SpectrallyNegativeLevy.generatorIntegrand U p.1 p.2
  have hUmeas : Measurable U :=
    (avram_wave4_p2_source_scale_primitive_global_monotone X q W hW).measurable
  have hdU : deriv U = W :=
    avram_wave4_p2_unbounded_scale_primitive_global_deriv_eq_scale
      X hnbv q hq W hW
  have hderUmeas : Measurable (deriv U) := by
    rw [hdU]
    exact chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hind : Measurable
      (fun y : ℝ => (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hker : Measurable
      (fun p : ℝ × ℝ => SpectrallyNegativeLevy.generatorIntegrand U p.1 p.2) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    fun_prop
  have hmeas : Measurable f := by fun_prop
  have hAbs := avram_wave4_p2_unbounded_scale_primitive_weighted_jump_product_integrable
    X hX hnbv q hq W hW θ hθ hqθ
  have hAbsInt :
      Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        |SpectrallyNegativeLevy.generatorIntegrand U p.1 p.2|) (μ.prod ν) := hAbs
  change Integrable f (μ.prod ν)
  apply hAbsInt.mono' hmeas.aestronglyMeasurable
  filter_upwards with p
  dsimp [f]
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _), le_refl]
