-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_weighted_jump_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:57:03.442622+00:00
-- url     : https://prove2.me/submissions/41f595e4-3713-40cb-bab9-f4c3c07e7269

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_small_jump_full_weighted_quadratic
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_scale_primitive_largejump_weighted_section_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_weighted_kernel_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_weighted_curvature_L1
import Theorems.Thm_AvramDividend_Classical_integrable_prod_of_slice_norm_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
/-- Genuine full small+large compensated primitive kernel product L1. -/
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
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) p.1 p.2|)
      ((volume.restrict (Ioi (0 : ℝ))).prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-(θ * p.1)) * |SpectrallyNegativeLevy.generatorIntegrand U p.1 p.2|
  haveI : SFinite ν := levy_negative_jump_measure_sFinite X
  have hθ0 : 0 ≤ θ := le_of_lt hθ
  have hmeas : Measurable f := by
    simpa only [f, U, neg_mul] using
      (avram_wave4_p2_unbounded_scale_primitive_weighted_kernel_joint_measurable
        X hnbv q hq W hW θ)
  have hf : AEStronglyMeasurable f (μ.prod ν) := hmeas.aestronglyMeasurable
  have hfnorm (p : ℝ × ℝ) : ‖f p‖ = f p := by
    simp only [f, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
  have hnorm_meas : AEStronglyMeasurable
      (fun y : ℝ => ∫ x, ‖f (x,y)‖ ∂μ) ν := by
    have hm : Measurable (fun p : ℝ × ℝ => ‖f p‖) := hmeas.norm
    exact (StronglyMeasurable.integral_prod_left
      (μ := μ) hm.stronglyMeasurable).aestronglyMeasurable
  have hminfull : Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    have hm : AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by fun_prop
    have hnn : 0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
      filter_upwards with y
      positivity
    exact (lintegral_ofReal_ne_top_iff_integrable hm hnn).mp (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν := hminfull.mono_measure Measure.restrict_le_self
  let M : ℝ := ∫ u : ℝ, Real.exp (-θ*u) *
    |(Ioi (0 : ℝ)).indicator (deriv W) u|
  have hM : 0 ≤ M := by
    dsimp [M]; apply MeasureTheory.integral_nonneg; intro u; positivity
  let L : ℝ := (X.ψ θ - q)⁻¹ / θ
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hW1 : 0 ≤ W 1 := hW.2.1 1 (by norm_num)
  let C : ℝ := W 1 + M / 2 + L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hneg : ∀ᵐ y ∂ν, y < 0 := by
    simpa only [ν, mem_Iio] using (ae_restrict_mem measurableSet_Iio :
      ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))), y ∈ Iio (0 : ℝ))
  have hsection_info (y : ℝ) (hy : y < 0) :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ*x)) *
          |SpectrallyNegativeLevy.generatorIntegrand U x y|)
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        |SpectrallyNegativeLevy.generatorIntegrand U x y|) ≤
        C * min 1 (y ^ 2) := by
    by_cases hsmall : -1 < y
    · have hr0 : 0 < -y := by linarith
      have hr1 : -y < 1 := by linarith
      have hs0 :=
        avram_wave4_p2_scale_primitive_small_jump_full_weighted_quadratic
          X hX q hq W hW (-y) θ hr0 hr1 hθ0 hqθ
      have hsI : IntegrableOn
          (fun x : ℝ => Real.exp (-(θ*x)) *
            |SpectrallyNegativeLevy.generatorIntegrand U x y|)
          (Ioi (0 : ℝ)) volume := by
        simpa only [neg_neg, U] using hs0.1
      have hsB :
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
            |SpectrallyNegativeLevy.generatorIntegrand U x y|) ≤
            (W 1 + M / 2) * y ^ 2 := by
        have hb := hs0.2
        simp only [neg_neg, neg_sq] at hb
        change (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
          |SpectrallyNegativeLevy.generatorIntegrand U x y|) ≤
          W 1 * y^2 + (y^2/2)*M at hb
        calc
          _ ≤ W 1 * y^2 + (y^2/2)*M := hb
          _ = (W 1 + M/2)*y^2 := by ring
      have hs := And.intro hsI hsB
      have hsq : y ^ 2 ≤ 1 := by nlinarith
      have hminval : min 1 (y ^ 2) = y ^ 2 := min_eq_right hsq
      refine ⟨hs.1, ?_⟩
      calc
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
            |SpectrallyNegativeLevy.generatorIntegrand U x y|) ≤
              (W 1 + M / 2) * y^2 := hs.2
        _ ≤ C * min 1 (y^2) := by
          rw [hminval]
          dsimp [C]
          nlinarith [mul_nonneg hL (sq_nonneg y)]
    · have hr : 1 ≤ -y := by linarith
      have hl0 := avram_wave4_05a_scale_primitive_largejump_weighted_section_integrable
        X q W hW θ hθ hqθ (-y) hr
      have hl : IntegrableOn
          (fun x : ℝ => Real.exp (-(θ*x)) *
            |SpectrallyNegativeLevy.generatorIntegrand U x y|)
          (Ioi (0 : ℝ)) volume ∧
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
            |SpectrallyNegativeLevy.generatorIntegrand U x y|) ≤ L := by
        simpa only [neg_neg, L] using hl0
      have hsq : 1 ≤ y ^ 2 := by nlinarith
      have hminval : min 1 (y ^ 2) = 1 := min_eq_left hsq
      refine ⟨hl.1, ?_⟩
      calc
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
          |SpectrallyNegativeLevy.generatorIntegrand U x y|) ≤ L := hl.2
        _ ≤ C * min 1 (y ^ 2) := by
          rw [hminval, mul_one]
          dsimp [C]
          linarith [div_nonneg hM (by norm_num : (0 : ℝ) ≤ 2)]
  have hsections : ∀ᵐ y ∂ν, Integrable (fun x => f (x,y)) μ := by
    filter_upwards [hneg] with y hy
    change IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
      |SpectrallyNegativeLevy.generatorIntegrand U x y|) (Ioi (0 : ℝ)) volume
    exact (hsection_info y hy).1
  have hdom : ∀ᵐ y ∂ν,
      (∫ x, ‖f (x,y)‖ ∂μ) ≤ C * min 1 (y ^ 2) := by
    filter_upwards [hneg] with y hy
    have hs := (hsection_info y hy).2
    calc
      (∫ x, ‖f (x,y)‖ ∂μ) = ∫ x, f (x,y) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact hfnorm (x,y)
      _ ≤ C * min 1 (y ^ 2) := by
        exact hs
  change Integrable f (μ.prod ν)
  exact integrable_prod_of_slice_norm_quadratic_bound
    μ ν f C hf hsections hnorm_meas hmin hdom
