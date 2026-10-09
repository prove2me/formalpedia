-- Prove2me | solution 1 for GaussianMatrix.inv_chi_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:41:29.156779+00:00
-- url     : https://prove2.me/submissions/b163a2f8-53a0-48dd-90a9-dc5128530953

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Real Set

/-- One-dimensional Gaussian integral: `E[exp(-((u-1)/2) Y²)] = u^{-1/2}` for `Y ~ N(0,1)`. -/
lemma icm_gauss_exp (u : ℝ) (hu : 0 < u) :
    ∫ y, Real.exp (-((u - 1) / 2) * y ^ 2) ∂(gaussianReal 0 1) = u ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h : ∀ x : ℝ, (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (-((u - 1) / 2) * x ^ 2)
      = (√(2 * π))⁻¹ * rexp (-(u / 2) * x ^ 2) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h2 : π / (u / 2) = (2 * π) / u := by field_simp
  rw [h2, Real.sqrt_div (by positivity), Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : √(2 * π) ≠ 0 := by positivity
  field_simp

/-- Laplace transform of the chi-square sum: `E[exp(-((u-1)/2) ∑ Xⱼ²)] = u^{-d/2}`. -/
lemma icm_laplace (d : ℕ) (u : ℝ) (hu : 0 < u) :
    ∫ x : Fin d → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = u ^ (-((d : ℝ) / 2)) := by
  have h : ∀ x : Fin d → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      = ∏ j, Real.exp (-((u - 1) / 2) * x j ^ 2) := by
    intro x; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (fun _ y => Real.exp (-((u - 1) / 2) * y ^ 2))]
  simp only [icm_gauss_exp u hu, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1; ring

/-- `1/S = ∫_1^∞ exp(-((u-1)/2) S)/2 du` for `S > 0`. -/
lemma icm_inv_repr (S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun u : ℝ => Real.exp (-((u - 1) / 2) * S) / 2) (Ioi 1) ∧
    ∫ u in Ioi 1, Real.exp (-((u - 1) / 2) * S) / 2 = S⁻¹ := by
  have h : ∀ u : ℝ, Real.exp (-((u - 1) / 2) * S) / 2
      = Real.exp ((-(S / 2)) * u) * (Real.exp (S / 2) / 2) := by
    intro u; rw [mul_div_assoc', ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  have hneg : -(S / 2) < 0 := by linarith
  refine ⟨(integrableOn_exp_mul_Ioi hneg 1).mul_const _, ?_⟩
  rw [integral_mul_const, integral_exp_mul_Ioi hneg]
  have he : rexp (-(S / 2)) * rexp (S / 2) = 1 := by rw [← Real.exp_add]; simp
  have hS0 : S ≠ 0 := hS.ne'
  rw [mul_one, show -rexp (-(S / 2)) / -(S / 2) * (rexp (S / 2) / 2)
    = (rexp (-(S / 2)) * rexp (S / 2)) / S by field_simp, he, one_div]

lemma icm_sum_pos_ae {d : ℕ} (hd : 1 ≤ d) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1), 0 < ∑ j, x j ^ 2 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hnull : (Measure.pi fun _ : Fin d => gaussianReal 0 1)
      (Function.eval (⟨0, hd⟩ : Fin d) ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [this] with x hx
  have hx0 : x ⟨0, hd⟩ ≠ 0 := by simpa using hx
  have h1 : x ⟨0, hd⟩ ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ _)
  have h2 : 0 < x ⟨0, hd⟩ ^ 2 := by positivity
  linarith

lemma icm_lintegral {d : ℕ} (hd : 3 ≤ d) :
    ∫⁻ x, ENNReal.ofReal (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = ENNReal.ofReal (1 / ((d : ℝ) - 2)) := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1 with hμ
  set K : (Fin d → ℝ) → ℝ → ℝ := fun x u => Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2) / 2 with hK
  have hK_cont : Continuous (Function.uncurry K) := by
    simp only [hK]; fun_prop
  -- step 1: inner representation
  have step1 : ∀ᵐ x ∂μ, ENNReal.ofReal (∑ j, x j ^ 2)⁻¹
      = ∫⁻ u in Ioi 1, ENNReal.ofReal (K x u) := by
    filter_upwards [icm_sum_pos_ae (by omega : 1 ≤ d)] with x hx
    obtain ⟨hint, hval⟩ := icm_inv_repr _ hx
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => by positivity)]
  rw [lintegral_congr_ae step1]
  rw [lintegral_lintegral_swap (hK_cont.measurable.ennreal_ofReal.aemeasurable)]
  -- step 2: inner integral over x
  have step2 : ∀ u ∈ Ioi (1 : ℝ), ∫⁻ x, ENNReal.ofReal (K x u) ∂μ
      = ENNReal.ofReal (u ^ (-((d : ℝ) / 2)) / 2) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hmeas : Measurable fun x => K x u :=
      (hK_cont.comp (Continuous.prodMk_left u)).measurable
    have hint : Integrable (fun x => K x u) μ := by
      refine (integrable_const (1 / 2 : ℝ)).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hS : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have : -((u - 1) / 2) * ∑ j, x j ^ 2 ≤ 0 := by
        have : 0 ≤ (u - 1) / 2 := by have := hu.out; linarith
        nlinarith
      have := Real.exp_le_one_iff.mpr this
      simp only [hK]; linarith
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    simp only [hK]
    rw [integral_div, icm_laplace d u hu0]
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  -- step 3: the outer integral
  have ha : -((d : ℝ) / 2) < -1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hint3 : IntegrableOn (fun u : ℝ => u ^ (-((d : ℝ) / 2)) / 2) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha one_pos).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint3]
  · congr 1
    rw [integral_div, integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow]
    have : (d : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have : -((d : ℝ) / 2) + 1 ≠ 0 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have : (2 : ℝ) - d ≠ 0 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    field_simp
    linear_combination inv_mul_cancel₀ this
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    positivity

theorem icm_main {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / ((d : ℝ) - 2) := by
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin d => gaussianReal 0 1]
      (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun x =>
      inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hmeas : Measurable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
  have hpos : (0 : ℝ) ≤ 1 / ((d : ℝ) - 2) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_nonneg zero_le_one; linarith
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, icm_lintegral hd]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, icm_lintegral hd,
      ENNReal.toReal_ofReal hpos]

end GaussianMatrix

open GaussianMatrix

theorem solution {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = 1 / ((d : ℝ) - 2) :=
  icm_main hd
