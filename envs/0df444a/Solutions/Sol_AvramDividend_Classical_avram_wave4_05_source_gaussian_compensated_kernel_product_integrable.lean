-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_gaussian_compensated_kernel_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:14:27.133917+00:00
-- url     : https://prove2.me/submissions/5075cc05-6646-4f59-8a0a-aa2d0afc56c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_gaussian_global_smalljump_splice
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_largejump_weighted_section_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_weighted_jump_section_norm_measurable
import Theorems.Thm_AvramDividend_Classical_integrable_prod_of_slice_norm_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Source Gaussian compensated generator kernel, signed product L¹. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ) (F : ℝ → ℝ)
    (hFpoint : ∀ u : ℝ, 0 < u → F u = iteratedDeriv 2 W u)
    (hFc : ContinuousOn F (Ioi (0 : ℝ))) (hFm : Measurable F)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hFi : Integrable (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
      SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let f : ℝ × ℝ → ℝ := fun p => Real.exp (-(θ * p.1)) *
    SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2
  haveI : SFinite ν := levy_negative_jump_measure_sFinite X
  obtain ⟨C, hC, hsmall⟩ :=
    avram_wave4_05_source_gaussian_global_smalljump_splice X hX q hq W hW hσ F hFpoint hFc hFm
  have hsmallθ := hsmall θ hθ hFi
  let M : ℝ := ∫ u : ℝ, Real.exp (-θ * u) * |F u|
  have hM : 0 ≤ M := by
    dsimp [M]
    apply integral_nonneg
    intro u
    positivity
  let L : ℝ := (X.ψ θ - q)⁻¹
  have hL : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr (le_of_lt (sub_pos.mpr hqθ))
  let Ctot : ℝ := C + M / 2 + L
  have hmeas : AEStronglyMeasurable f (μ.prod ν) := by
    exact avram_wave4_05_source_scale_weighted_signed_kernel_product_measurable X q W hW θ
  have hnorm_meas : AEStronglyMeasurable
      (fun y : ℝ => ∫ x, ‖f (x,y)‖ ∂μ) ν := by
    exact avram_wave4_05_source_weighted_jump_section_norm_measurable X q W hW θ
  have hminfull : Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    have hmin_meas : AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by fun_prop
    have hmin_nonneg : 0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
      filter_upwards with y
      positivity
    exact (lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν := hminfull.mono_measure Measure.restrict_le_self
  have hscale : Measurable W := chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hd : Measurable (deriv W) := measurable_deriv W
  have hind : Measurable (fun y : ℝ =>
      (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hhexp (x : ℝ) : Real.exp (-(θ * x)) = Real.exp (-θ * x) := by
    congr 1
    ring
  have hslice_eq (y : ℝ) : (fun x : ℝ => ‖f (x,y)‖) =
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x y|) := by
    funext x
    simp only [f, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
  have hslice_meas (y : ℝ) : AEStronglyMeasurable (fun x : ℝ => f (x,y)) μ := by
    have hm : Measurable (fun x : ℝ => f (x,y)) := by
      dsimp [f]
      unfold SpectrallyNegativeLevy.generatorIntegrand
      fun_prop
    exact hm.aestronglyMeasurable
  have hneg : ∀ᵐ y ∂ν, y < 0 := by
    simpa only [ν, mem_Iio] using (ae_restrict_mem measurableSet_Iio :
      ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))), y ∈ Iio (0 : ℝ))
  have hsection_info (y : ℝ) (hy : y < 0) :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x y|) (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤ Ctot * min 1 (y ^ 2) := by
    by_cases hsmall_y : -1 < y
    · have hr : 0 < -y := by linarith
      have hr1 : -y < 1 := by linarith
      have hs0 := hsmallθ (-y) hr hr1
      have hs : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) (Ioi (0 : ℝ)) volume ∧
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤ (C + M / 2) * y ^ 2 := by
        simpa only [neg_neg, neg_sq, hhexp, M] using hs0
      have hsq : y ^ 2 ≤ 1 := by nlinarith
      have hminval : min 1 (y ^ 2) = y ^ 2 := min_eq_right hsq
      refine ⟨hs.1, ?_⟩
      calc
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤
          (C + M / 2) * y ^ 2 := hs.2
        _ ≤ Ctot * min 1 (y ^ 2) := by
          rw [hminval]
          dsimp [Ctot]
          nlinarith [mul_nonneg hL (sq_nonneg y)]
    · have hr : 1 ≤ -y := by linarith
      have hl0 :=
        avram_wave4_05_source_largejump_weighted_section_integrable
          X q W hW θ hθ hqθ (-y) hr
      have hl : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) (Ioi (0 : ℝ)) volume ∧
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤ L := by
        simpa only [neg_neg, L] using hl0
      have hsq : 1 ≤ y ^ 2 := by nlinarith
      have hminval : min 1 (y ^ 2) = 1 := min_eq_left hsq
      refine ⟨hl.1, ?_⟩
      calc
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y|) ≤ L := hl.2
        _ ≤ Ctot * min 1 (y ^ 2) := by
          rw [hminval]
          dsimp [Ctot]
          nlinarith
  have hsections : ∀ᵐ y ∂ν, Integrable (fun x => f (x,y)) μ := by
    filter_upwards [hneg] with y hy
    have hi := (hsection_info y hy).1
    have hnorm : Integrable (fun x : ℝ => ‖f (x,y)‖) μ := by
      change IntegrableOn (fun x : ℝ => ‖f (x,y)‖)
        (Ioi (0 : ℝ)) volume
      rw [hslice_eq y]
      exact hi
    exact (integrable_norm_iff (hslice_meas y)).1 hnorm
  have hdom : ∀ᵐ y ∂ν, (∫ x, ‖f (x,y)‖ ∂μ) ≤
      Ctot * min 1 (y ^ 2) := by
    filter_upwards [hneg] with y hy
    have hi := (hsection_info y hy).2
    have heq :
        (∫ x, ‖f (x,y)‖ ∂μ) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          |SpectrallyNegativeLevy.generatorIntegrand W x y| := by
      change (∫ x in Ioi (0 : ℝ), ‖f (x,y)‖) = _
      rw [hslice_eq y]
    rw [heq]
    exact hi
  exact integrable_prod_of_slice_norm_quadratic_bound μ ν f Ctot hmeas hsections hnorm_meas hmin hdom
