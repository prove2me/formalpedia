-- Prove2me | solution 1 for GaussianMatrix.inv_sq_chi_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:18:15.10627+00:00
-- url     : https://prove2.me/submissions/88cd0b01-6968-461b-ab80-a840ba808d1f

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Real Set Filter Topology

/-- One-dimensional Gaussian integral: `E[exp(-((u-1)/2) Y²)] = u^{-1/2}` for `Y ~ N(0,1)`. -/
lemma iscm_gauss_exp (u : ℝ) (hu : 0 < u) :
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
lemma iscm_laplace (d : ℕ) (u : ℝ) (hu : 0 < u) :
    ∫ x : Fin d → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = u ^ (-((d : ℝ) / 2)) := by
  have h : ∀ x : Fin d → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      = ∏ j, Real.exp (-((u - 1) / 2) * x j ^ 2) := by
    intro x; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (fun _ y => Real.exp (-((u - 1) / 2) * y ^ 2))]
  simp only [iscm_gauss_exp u hu, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1; ring

/-- `1/S² = ∫_1^∞ ((u-1)/4) exp(-((u-1)/2) S) du` for `S > 0`. -/
lemma iscm_inv_sq_repr (S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun u : ℝ => (u - 1) / 4 * Real.exp (-((u - 1) / 2) * S)) (Ioi 1) ∧
    ∫ u in Ioi 1, (u - 1) / 4 * Real.exp (-((u - 1) / 2) * S) = (S⁻¹) ^ 2 := by
  have hS0 : S ≠ 0 := hS.ne'
  set g : ℝ → ℝ := fun u => -((u - 1) / (2 * S) + 1 / S ^ 2) * Real.exp (-((u - 1) / 2) * S)
    with hg
  have hderiv : ∀ x ∈ Ici (1 : ℝ),
      HasDerivAt g ((x - 1) / 4 * Real.exp (-((x - 1) / 2) * S)) x := by
    intro x _
    have h1 : HasDerivAt (fun u : ℝ => -((u - 1) / (2 * S) + 1 / S ^ 2)) (-(1 / (2 * S))) x := by
      exact ((((hasDerivAt_id x).sub_const 1).div_const (2 * S)).add_const (1 / S ^ 2)).neg
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-((u - 1) / 2) * S))
        (Real.exp (-((x - 1) / 2) * S) * (-(1 / 2) * S)) x := by
      have : HasDerivAt (fun u : ℝ => -((u - 1) / 2) * S) (-(1 / 2) * S) x := by
        have := ((((hasDerivAt_id x).sub_const 1).div_const 2).neg).mul_const S
        simpa using this
      exact this.exp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ (x - 1) / 4 * Real.exp (-((x - 1) / 2) * S) := by
    intro x hx
    have : 0 ≤ x - 1 := by have := hx.out; linarith
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    -- `g u = -(1/S²) (t + 1) e^{-t}` with `t = (u-1) S / 2 → ∞`
    have ht : Tendsto (fun u : ℝ => (u - 1) * S / 2) atTop atTop := by
      have : Tendsto (fun u : ℝ => u - 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
      exact (this.atTop_mul_const hS).atTop_div_const (by norm_num)
    have h0 : Tendsto (fun t : ℝ => t ^ 1 * Real.exp (-t) + t ^ 0 * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
        (tendsto_pow_mul_exp_neg_atTop_nhds_zero 0)
    have h1 := (h0.comp ht).const_mul (-(1 / S ^ 2))
    rw [mul_zero] at h1
    refine h1.congr fun u => ?_
    simp only [hg, Function.comp_apply, pow_one, pow_zero, one_mul]
    have : -((u - 1) * S / 2) = -((u - 1) / 2) * S := by ring
    rw [this]
    field_simp
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn hlim]
  simp only [hg, sub_self, zero_div, neg_zero, zero_mul, Real.exp_zero, mul_one, zero_add]
  field_simp
  ring

lemma iscm_sum_pos_ae {d : ℕ} (hd : 1 ≤ d) :
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

lemma iscm_lintegral {d : ℕ} (hd : 5 ≤ d) :
    ∫⁻ x, ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ 2) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = ENNReal.ofReal (1 / (((d : ℝ) - 2) * ((d : ℝ) - 4))) := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1 with hμ
  set K : (Fin d → ℝ) → ℝ → ℝ :=
    fun x u => (u - 1) / 4 * Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2) with hK
  have hK_cont : Continuous (Function.uncurry K) := by
    simp only [hK]; fun_prop
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  -- step 1: inner representation
  have step1 : ∀ᵐ x ∂μ, ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ 2)
      = ∫⁻ u in Ioi 1, ENNReal.ofReal (K x u) := by
    filter_upwards [iscm_sum_pos_ae (by omega : 1 ≤ d)] with x hx
    obtain ⟨hint, hval⟩ := iscm_inv_sq_repr _ hx
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have : 0 ≤ u - 1 := by have := hu.out; linarith
    simp only [Pi.zero_apply]
    positivity
  rw [lintegral_congr_ae step1]
  rw [lintegral_lintegral_swap (hK_cont.measurable.ennreal_ofReal.aemeasurable)]
  -- step 2: inner integral over x
  have step2 : ∀ u ∈ Ioi (1 : ℝ), ∫⁻ x, ENNReal.ofReal (K x u) ∂μ
      = ENNReal.ofReal ((u - 1) / 4 * u ^ (-((d : ℝ) / 2))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hu1 : 0 ≤ u - 1 := by have := hu.out; linarith
    have hmeas : Measurable fun x => K x u :=
      (hK_cont.comp (Continuous.prodMk_left u)).measurable
    have hint : Integrable (fun x => K x u) μ := by
      refine (integrable_const ((u - 1) / 4)).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hK]; positivity)]
      have hS : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have : -((u - 1) / 2) * ∑ j, x j ^ 2 ≤ 0 := by
        have : 0 ≤ (u - 1) / 2 := by linarith
        nlinarith
      have := Real.exp_le_one_iff.mpr this
      simp only [hK]
      have h4 : 0 ≤ (u - 1) / 4 := by linarith
      nlinarith
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by simp only [hK]; positivity)]
    congr 1
    simp only [hK]
    rw [integral_const_mul, iscm_laplace d u hu0]
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  -- step 3: the outer integral
  have ha : -((d : ℝ) / 2) < -1 := by linarith
  have ha' : -((d : ℝ) / 2) + 1 < -1 := by linarith
  have hsplit : ∀ u ∈ Ioi (1 : ℝ), (u - 1) / 4 * u ^ (-((d : ℝ) / 2))
      = u ^ (-((d : ℝ) / 2) + 1) / 4 - u ^ (-((d : ℝ) / 2)) / 4 := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    rw [Real.rpow_add_one hu0.ne']
    ring
  have hintA : IntegrableOn (fun u : ℝ => u ^ (-((d : ℝ) / 2) + 1) / 4) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha' one_pos).div_const _
  have hintB : IntegrableOn (fun u : ℝ => u ^ (-((d : ℝ) / 2)) / 4) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha one_pos).div_const _
  have hint3 : IntegrableOn (fun u : ℝ => (u - 1) / 4 * u ^ (-((d : ℝ) / 2))) (Ioi 1) :=
    (hintA.sub hintB).congr_fun (fun u hu => (hsplit u hu).symm) measurableSet_Ioi
  rw [← ofReal_integral_eq_lintegral_ofReal hint3]
  · congr 1
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hintA hintB,
      integral_div, integral_div, integral_Ioi_rpow_of_lt ha one_pos,
      integral_Ioi_rpow_of_lt ha' one_pos, Real.one_rpow, Real.one_rpow]
    have h1 : (d : ℝ) - 2 ≠ 0 := by linarith
    have h2 : (d : ℝ) - 4 ≠ 0 := by linarith
    have h3 : -((d : ℝ) / 2) + 1 ≠ 0 := by linarith
    have h4 : -((d : ℝ) / 2) + 1 + 1 ≠ 0 := by linarith
    have h5 : (4 : ℝ) - d ≠ 0 := by linarith
    have h6 : (2 : ℝ) - d ≠ 0 := by linarith
    rw [show -((d : ℝ) / 2) + 1 + 1 = (4 - d) / 2 by ring,
      show -((d : ℝ) / 2) + 1 = (2 - d) / 2 by ring]
    field_simp
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have : 0 ≤ u - 1 := by have := hu.out; linarith
    positivity

theorem iscm_main {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ 2)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) := by
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin d => gaussianReal 0 1]
      (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ 2) :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hmeas : Measurable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ 2) := by fun_prop
  have hpos : (0 : ℝ) ≤ 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) := by
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_nonneg zero_le_one; nlinarith
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, iscm_lintegral hd]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, iscm_lintegral hd,
      ENNReal.toReal_ofReal hpos]

end GaussianMatrix

open GaussianMatrix

theorem solution {d : ℕ} (hd : 5 ≤ d) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ 2)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / (((d : ℝ) - 2) * ((d : ℝ) - 4)) :=
  iscm_main hd
