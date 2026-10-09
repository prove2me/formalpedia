-- Prove2me | solution 1 for GaussianMatrix.chi_square_neg_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:59:04.769983+00:00
-- url     : https://prove2.me/submissions/f8ee9ec9-f451-48e9-a892-b86335dc2f87

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Real Set

/-- One-dimensional Gaussian integral: `E[exp(-((u-1)/2) Y²)] = u^{-1/2}` for `Y ~ N(0,1)`. -/
lemma cnm_gauss_exp (u : ℝ) (hu : 0 < u) :
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
lemma cnm_laplace (d : ℕ) (u : ℝ) (hu : 0 < u) :
    ∫ x : Fin d → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) = u ^ (-((d : ℝ) / 2)) := by
  have h : ∀ x : Fin d → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      = ∏ j, Real.exp (-((u - 1) / 2) * x j ^ 2) := by
    intro x; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (fun _ y => Real.exp (-((u - 1) / 2) * y ^ 2))]
  simp only [cnm_gauss_exp u hu, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1; ring

lemma cnm_sum_pos_ae {d : ℕ} (hd : 1 ≤ d) :
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

/-- Euler's integral in `lintegral` form:
`∫_0^∞ c t^{a-1} e^{-rt} dt = c (1/r)^a Γ(a)` for `a, r > 0`, `c ≥ 0`. -/
lemma cnm_gamma_lintegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * (t ^ (a - 1) * Real.exp (-(r * t))))
      = ENNReal.ofReal (c * ((1 / r) ^ a * Gamma a)) := by
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  have hpos : 0 < (1 / r) ^ a * Gamma a := by
    have : 0 < Gamma a := Gamma_pos_of_pos ha
    positivity
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hI]; exact hpos.ne')
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul c), integral_const_mul, hI]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have : 0 ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
  positivity

/-- The negative moment of a chi-square variable, in `lintegral` form. -/
lemma cnm_lintegral {d : ℕ} (q : ℝ) (hq : 0 < q) (hqd : q < (d : ℝ) / 2) :
    ∫⁻ x, ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ q) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = ENNReal.ofReal (Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Gamma ((d : ℝ) / 2))) := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1 with hμ
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hqd; linarith
    · exact h
  have hx0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hGq : 0 < Gamma q := Gamma_pos_of_pos hq
  have hGd : 0 < Gamma ((d : ℝ) / 2) := Gamma_pos_of_pos hx0
  set S : (Fin d → ℝ) → ℝ := fun x => ∑ j, x j ^ 2 with hS
  have hSm : Measurable S := by fun_prop
  -- step 1: Euler representation of `S^{-q}`
  set K : (Fin d → ℝ) → ℝ → ENNReal :=
    fun x v => ENNReal.ofReal ((Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))) with hK
  have step1 : ∀ᵐ x ∂μ, ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ q) = ∫⁻ v in Ioi 0, K x v := by
    filter_upwards [cnm_sum_pos_ae hd1] with x hx
    simp only [hK]
    rw [cnm_gamma_lintegral hq hx (Gamma q)⁻¹ (inv_nonneg.mpr hGq.le)]
    congr 1
    rw [one_div]
    field_simp
  rw [lintegral_congr_ae step1]
  have hKm : Measurable (Function.uncurry K) := by
    simp only [hK, hS]
    fun_prop
  rw [lintegral_lintegral_swap hKm.aemeasurable]
  -- step 2: integrate out `x` (Laplace transform)
  have step2 : ∀ v ∈ Ioi (0 : ℝ), ∫⁻ x, K x v ∂μ
      = ENNReal.ofReal ((Gamma q)⁻¹ * v ^ (q - 1) * (1 + 2 * v) ^ (-((d : ℝ) / 2))) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have hc : 0 ≤ (Gamma q)⁻¹ * v ^ (q - 1) :=
      mul_nonneg (inv_nonneg.mpr hGq.le) (Real.rpow_nonneg hv0.le _)
    have hmeas : Measurable fun x => (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v))) := by
      simp only [hS]; fun_prop
    have hint : Integrable (fun x => (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))) μ := by
      refine (integrable_const ((Gamma q)⁻¹ * v ^ (q - 1))).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      have hSx : 0 ≤ S x := Finset.sum_nonneg fun j _ => sq_nonneg _
      have he : Real.exp (-(S x * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))
          = ((Gamma q)⁻¹ * v ^ (q - 1)) * Real.exp (-(S x * v)) := by ring
        _ ≤ ((Gamma q)⁻¹ * v ^ (q - 1)) * 1 := by gcongr
        _ = _ := mul_one _
    simp only [hK]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    have hlap := cnm_laplace d (1 + 2 * v) (by linarith)
    have hfun : ∀ x : Fin d → ℝ, (Gamma q)⁻¹ * (v ^ (q - 1) * Real.exp (-(S x * v)))
        = ((Gamma q)⁻¹ * v ^ (q - 1)) *
          Real.exp (-((1 + 2 * v - 1) / 2) * ∑ j, x j ^ 2) := by
      intro x; simp only [hS]; ring_nf
    simp_rw [hfun]
    rw [integral_const_mul, hlap]
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  -- step 3: Euler representation of `(1+2v)^{-d/2}`
  set Gd := Gamma ((d : ℝ) / 2) with hGd'
  set L : ℝ → ℝ → ENNReal := fun v w => ENNReal.ofReal
    ((Gamma q)⁻¹ * v ^ (q - 1) * Gd⁻¹ * (w ^ ((d : ℝ) / 2 - 1) * Real.exp (-((1 + 2 * v) * w))))
    with hL
  have step3 : ∀ v ∈ Ioi (0 : ℝ),
      ENNReal.ofReal ((Gamma q)⁻¹ * v ^ (q - 1) * (1 + 2 * v) ^ (-((d : ℝ) / 2)))
        = ∫⁻ w in Ioi 0, L v w := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have h12 : (0 : ℝ) < 1 + 2 * v := by linarith
    simp only [hL]
    rw [cnm_gamma_lintegral hx0 h12 _ (by
      have := Real.rpow_nonneg hv0.le (q - 1); positivity)]
    congr 1
    rw [one_div, Real.inv_rpow h12.le, ← Real.rpow_neg h12.le]
    field_simp
    exact hGd'
  rw [setLIntegral_congr_fun measurableSet_Ioi step3]
  have hLm : Measurable (Function.uncurry L) := by
    simp only [hL]
    fun_prop
  rw [lintegral_lintegral_swap hLm.aemeasurable]
  -- step 4: integrate out `v`
  have step4 : ∀ w ∈ Ioi (0 : ℝ), ∫⁻ v in Ioi 0, L v w
      = ENNReal.ofReal ((Gd⁻¹ * (2 ^ q)⁻¹) *
          (w ^ ((d : ℝ) / 2 - q - 1) * Real.exp (-(1 * w)))) := by
    intro w hw
    have hw0 : (0 : ℝ) < w := hw
    have hfun : ∀ v : ℝ, L v w = ENNReal.ofReal
        (((Gamma q)⁻¹ * Gd⁻¹ * w ^ ((d : ℝ) / 2 - 1) * Real.exp (-w)) *
          (v ^ (q - 1) * Real.exp (-((2 * w) * v)))) := by
      intro v
      simp only [hL]
      congr 1
      have : Real.exp (-((1 + 2 * v) * w)) = Real.exp (-w) * Real.exp (-((2 * w) * v)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    simp_rw [hfun]
    rw [cnm_gamma_lintegral hq (by positivity) _ (by
      have := Real.rpow_nonneg hw0.le ((d : ℝ) / 2 - 1); positivity)]
    congr 1
    have h1 : (1 / (2 * w)) ^ q = (2 ^ q)⁻¹ * w ^ (-q) := by
      rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow (by norm_num) hw0.le,
        Real.rpow_neg hw0.le, mul_inv]
    have h2 : w ^ ((d : ℝ) / 2 - 1) * w ^ (-q) = w ^ ((d : ℝ) / 2 - q - 1) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    rw [h1, one_mul]
    calc (Gamma q)⁻¹ * Gd⁻¹ * w ^ ((d : ℝ) / 2 - 1) * Real.exp (-w) *
          ((2 ^ q)⁻¹ * w ^ (-q) * Gamma q)
        = ((Gamma q)⁻¹ * Gamma q) * Gd⁻¹ * (2 ^ q)⁻¹ *
          (w ^ ((d : ℝ) / 2 - 1) * w ^ (-q)) * Real.exp (-w) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hGq.ne', h2]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi step4]
  -- step 5: the last Gamma integral
  have ha : (0 : ℝ) < (d : ℝ) / 2 - q := by linarith
  rw [cnm_gamma_lintegral ha one_pos _ (by positivity)]
  congr 1
  rw [div_one, Real.one_rpow, one_mul]
  field_simp

end GaussianMatrix

open GaussianMatrix

theorem solution {d : ℕ} (q : ℝ) (hq : 0 ≤ q) (hqd : q < (d : ℝ) / 2) :
    Integrable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ q ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = Real.Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Real.Gamma ((d : ℝ) / 2)) := by
  rcases hq.eq_or_lt with h0 | hq0
  · subst h0
    have hx0 : (0 : ℝ) < (d : ℝ) / 2 := hqd
    have hG := (Real.Gamma_pos_of_pos hx0).ne'
    simp only [Real.rpow_zero, sub_zero, one_mul]
    refine ⟨integrable_const _, ?_⟩
    rw [integral_const]
    simp [hG]
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : Fin d => gaussianReal 0 1]
      (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q) :=
    Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)) _
  have hmeas : Measurable (fun x : Fin d → ℝ => ((∑ j, x j ^ 2)⁻¹) ^ q) := by fun_prop
  have hx0 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hpos : (0 : ℝ) ≤ Real.Gamma ((d : ℝ) / 2 - q) / (2 ^ q * Real.Gamma ((d : ℝ) / 2)) := by
    have := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < (d : ℝ) / 2 - q)
    have := Real.Gamma_pos_of_pos hx0
    positivity
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, cnm_lintegral q hq0 hqd]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable,
      cnm_lintegral q hq0 hqd, ENNReal.toReal_ofReal hpos]
