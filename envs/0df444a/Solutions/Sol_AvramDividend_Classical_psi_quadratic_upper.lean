-- Prove2me | solution 1 for AvramDividend.Classical.psi_quadratic_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:08:54.438756+00:00
-- url     : https://prove2.me/submissions/99187f26-b101-4384-8b45-43d86ad1bef1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_integrand_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.ψ θ ≤
      (|X.c| + X.σ ^ 2 / 2 +
        ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν) * θ ^ 2 := by
  let f : ℝ → ℝ := fun y =>
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y
  let g : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator (fun y : ℝ => θ ^ 2 * y ^ 2)
  have hmin_meas : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by fun_prop
  have hmin_nonneg : 0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y => le_min (by norm_num) (sq_nonneg y))
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmin_meas.aestronglyMeasurable hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hbound_int :
      Integrable (fun y : ℝ => θ ^ 2 * min 1 (y ^ 2)) X.ν :=
    hmin_int.const_mul _
  have hind_meas :
      Measurable (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hf_meas : Measurable f := by
    dsimp [f]
    fun_prop
  have hfg (y : ℝ) (hy : y < 0) :
      |f y| ≤ θ ^ 2 * min 1 (y ^ 2) ∧ f y ≤ g y := by
    simpa only [f, g] using negative_jump_integrand_bounds θ y hθ hy
  have hf_int : IntegrableOn f (Iio (0 : ℝ)) X.ν := by
    apply Integrable.mono' hbound_int.restrict hf_meas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with y hy
    simpa only [Real.norm_eq_abs] using (hfg y hy).1
  have hsubset : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) :=
    fun _ hy => hy.2
  have hsmall_int :
      IntegrableOn (fun y : ℝ => θ ^ 2 * y ^ 2) (Ioo (-1 : ℝ) 0) X.ν := by
    have hrestricted :
        IntegrableOn (fun y : ℝ => θ ^ 2 * min 1 (y ^ 2))
          (Ioo (-1 : ℝ) 0) X.ν := hbound_int.restrict
    refine hrestricted.congr_fun ?_ measurableSet_Ioo
    intro y hy
    have hy2 : y ^ 2 ≤ 1 := by
      have h : 0 ≤ (1 + y) * (1 - y) :=
        mul_nonneg (by linarith [hy.1]) (by linarith [hy.2])
      nlinarith
    simp only [min_eq_right hy2]
  have hg_int : IntegrableOn g (Iio (0 : ℝ)) X.ν := by
    change IntegrableOn
      ((Ioo (-1 : ℝ) 0).indicator (fun y : ℝ => θ ^ 2 * y ^ 2))
      (Iio (0 : ℝ)) X.ν
    rw [integrableOn_indicator_iff measurableSet_Ioo,
        Set.inter_eq_left.mpr hsubset]
    exact hsmall_int
  have hmono :
      (∫ y in Iio (0 : ℝ), f y ∂X.ν) ≤
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) := by
    apply integral_mono_ae hf_int hg_int
    exact ae_restrict_of_forall_mem measurableSet_Iio (fun y hy => (hfg y hy).2)
  have hgintegral :
      (∫ y in Iio (0 : ℝ), g y ∂X.ν) =
      θ ^ 2 * ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν := by
    change (∫ y in Iio (0 : ℝ),
      (Ioo (-1 : ℝ) 0).indicator (fun y : ℝ => θ ^ 2 * y ^ 2) y ∂X.ν) = _
    rw [integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict_of_subset hsubset,
        integral_const_mul]
  have hθ2 : θ ≤ θ ^ 2 := by nlinarith
  have hdrift : X.c * θ ≤ |X.c| * θ ^ 2 := by
    calc
      X.c * θ ≤ |X.c| * θ :=
        mul_le_mul_of_nonneg_right (le_abs_self X.c) (by linarith)
      _ ≤ |X.c| * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hθ2 (abs_nonneg X.c)
  calc
    X.ψ θ =
      X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        ∫ y in Iio (0 : ℝ), f y ∂X.ν := rfl
    _ ≤ X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        ∫ y in Iio (0 : ℝ), g y ∂X.ν := by linarith [hmono]
    _ = X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 +
        θ ^ 2 * ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν := by rw [hgintegral]
    _ ≤ (|X.c| + X.σ ^ 2 / 2 +
        ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν) * θ ^ 2 := by
      nlinarith [hdrift]
