-- Prove2me | solution 1 for FeynmanWick.integral_even_moment_gaussian_weight
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:51:43.056554+00:00
-- url     : https://prove2.me/submissions/23db9cb7-1510-407f-a5a2-8d1740d46c0b

import Mathlib
import Definitions.Def_FeynmanWickPairings

open MeasureTheory ProbabilityTheory
open FeynmanWick

theorem W3a_FeynmanWick_integral_gaussian_weight (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * x ^ 2) / 2) = Real.sqrt (2 * Real.pi / a) := by
  have h := integral_gaussian (a / 2)
  have e : (fun x : ℝ => Real.exp (-(a * x ^ 2) / 2)) = fun x => Real.exp (-(a / 2) * x ^ 2) := by
    funext x; congr 1; ring
  rw [e, h]
  congr 1
  field_simp

theorem solution (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-(a * x ^ 2) / 2)
      = (Nat.doubleFactorial (2 * n - 1) : ℝ) / a ^ n * Real.sqrt (2 * Real.pi / a) := by
  have h1 : ∀ x : ℝ, x ^ (2 * n) * Real.exp (-(a * x ^ 2) / 2)
      = |x| ^ (2 * n) * Real.exp (-(a * |x| ^ 2) / 2) := by
    intro x; rw [pow_mul, pow_mul, sq_abs]
  have h2 := integral_comp_abs (f := fun y : ℝ => y ^ (2 * n) * Real.exp (-(a * y ^ 2) / 2))
  beta_reduce at h2
  have h3 : ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-(a * x ^ 2) / 2)
      = ∫ x in Set.Ioi (0 : ℝ), x ^ (((2 * n : ℕ)) : ℝ) * Real.exp (-(a / 2) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [Real.rpow_natCast, Real.rpow_two, show -(a * x ^ 2) / 2 = -(a / 2) * x ^ 2 by ring]
  have hq : (-1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h4 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((2 * n : ℕ) : ℝ)) (b := a / 2)
    two_pos hq (by positivity)
  have hg : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
  have he : -(((2 * n : ℕ) : ℝ) + 1) / 2 = -((n : ℝ) + 1 / 2) := by push_cast; ring
  rw [hg, he, Real.Gamma_nat_add_half] at h4
  have ha2 : (0 : ℝ) < a / 2 := by positivity
  rw [Real.rpow_neg ha2.le, Real.rpow_add ha2, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow] at h4
  rw [integral_congr_ae (ae_of_all _ h1), h2, h3, h4]
  have hs : Real.sqrt (2 * Real.pi / a) = Real.sqrt Real.pi / Real.sqrt (a / 2) := by
    rw [← Real.sqrt_div' _ ha2.le]
    congr 1
    field_simp
  rw [hs]
  set t := Real.sqrt (a / 2) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr ha2
  have hat : a = 2 * t ^ 2 := by
    rw [ht, Real.sq_sqrt ha2.le]; ring
  have hat2 : a / 2 = t ^ 2 := by rw [hat]; ring
  rw [hat2, hat]
  field_simp
  ring

theorem W3a_FeynmanWick_gaussianReal_moment_even (v : NNReal) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) ∂(gaussianReal 0 v)
      = (Nat.doubleFactorial (2 * n - 1) : ℝ) * (v : ℝ) ^ n := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    rcases n with _ | n
    · simp
    · simp
  · rw [integral_gaussianReal_eq_integral_smul hv]
    have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    have e : ∀ x : ℝ, gaussianPDFReal 0 v x • x ^ (2 * n)
        = (Real.sqrt (2 * Real.pi * v))⁻¹ * (x ^ (2 * n) * Real.exp (-((1 / (v : ℝ)) * x ^ 2) / 2)) := by
      intro x
      simp only [gaussianPDFReal, smul_eq_mul, sub_zero]
      rw [show -x ^ 2 / (2 * (v : ℝ)) = -((1 / (v : ℝ)) * x ^ 2) / 2 by field_simp]
      ring
    rw [integral_congr_ae (ae_of_all _ e), integral_const_mul,
      solution _ (by positivity)]
    have hs : Real.sqrt (2 * Real.pi / (1 / (v : ℝ))) = Real.sqrt (2 * Real.pi * v) := by
      congr 1; field_simp
    rw [hs]
    have hp : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    rw [one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hvpos.ne')]

theorem W3a_FeynmanWick_map_neg {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) :
    μ.map (fun x => -x) = μ := by
  have hmean : ∫ x, x ∂μ = 0 := by
    refine PiLp.ext fun i => ?_
    have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm
      (IsGaussian.integrable_id (μ := μ))
    simpa [hcent] using h.symm
  have hmean' : μ[id] = 0 := by simpa using hmean
  refine Measure.ext_of_charFunDual ?_
  ext L
  have hL : (fun x : EuclideanSpace ℝ (Fin d) => -x)
      = ⇑(-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) := by
    funext x; simp
  rw [hL, charFunDual_map, IsGaussian.charFunDual_eq_of_integral_eq_zero hmean',
    IsGaussian.charFunDual_eq_of_integral_eq_zero hmean']
  have hc : ⇑(L.comp (-(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))))) = -⇑L := by
    funext x; simp
  rw [hc, variance_neg]

theorem W3a_FeynmanWick_gaussian_moment_odd_eq_zero {d n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsGaussian μ]
    (hcent : ∀ i : Fin d, ∫ x, x i ∂μ = 0) (k : Fin (2 * n + 1) → Fin d) :
    ∫ x, ∏ j : Fin (2 * n + 1), x (k j) ∂μ = 0 := by
  have hm := W3a_FeynmanWick_map_neg μ hcent
  have h1 : ∫ x, ∏ j : Fin (2 * n + 1), x (k j) ∂μ
      = ∫ x, ∏ j : Fin (2 * n + 1), (-x) (k j) ∂μ := by
    conv_lhs => rw [← hm]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∀ x : EuclideanSpace ℝ (Fin d),
      ∏ j : Fin (2 * n + 1), (-x) (k j) = -∏ j : Fin (2 * n + 1), x (k j) := by
    intro x
    simp only [PiLp.neg_apply]
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, Odd.neg_one_pow ⟨n, rfl⟩]
    ring
  simp_rw [h2, integral_neg] at h1
  linarith
