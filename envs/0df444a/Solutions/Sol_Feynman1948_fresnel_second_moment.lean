-- Prove2me | solution 1 for Feynman1948.fresnel_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:45:25.321325+00:00
-- url     : https://prove2.me/submissions/1a395e20-f162-4362-88f2-b78ffde73402

import Definitions.Def_Feynman1948_WaveEquation
import Theorems.Thm_Feynman1948_fresnel_zeroth_moment
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open Complex Filter MeasureTheory Topology Feynman1948

private theorem gaussian_sq_integral {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (-b * (x : ℂ) ^ 2)) =
      (2 * b)⁻¹ * ∫ x : ℝ, Complex.exp (-b * (x : ℂ) ^ 2) := by
  have hi0 := integrable_cexp_neg_mul_sq hb
  have hi2 : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (-b * (x : ℂ) ^ 2)) := by
    have hr : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b.re * x ^ 2)) := by
      simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
    refine ⟨by fun_prop, ?_⟩
    rw [← hasFiniteIntegral_norm_iff]
    have hn : (fun x : ℝ => ‖(x : ℂ) ^ 2 * Complex.exp (-b * (x : ℂ) ^ 2)‖) =
        (fun x : ℝ => x ^ 2 * Real.exp (-b.re * x ^ 2)) := by
      funext x
      rw [norm_mul, norm_pow, norm_cexp_neg_mul_sq]
      simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hn]
    exact hr.hasFiniteIntegral
  have hd (x : ℝ) : HasDerivAt
      (fun u : ℝ => (u : ℂ) * Complex.exp (-b * (u : ℂ) ^ 2))
      (Complex.exp (-b * (x : ℂ) ^ 2) -
        (2 * b) * ((x : ℂ) ^ 2 * Complex.exp (-b * (x : ℂ) ^ 2))) x := by
    convert ((hasDerivAt_id (x : ℂ)).mul
      (((hasDerivAt_pow 2 (x : ℂ)).const_mul (-b)).cexp)).comp_ofReal using 1 <;>
        first | rfl | (simp only [id_eq]; ring)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (hi0.sub (hi2.const_mul (2 * b))) (integrable_mul_cexp_neg_mul_sq hb)
  rw [integral_sub hi0 (hi2.const_mul (2 * b)), integral_const_mul] at hzero
  have hbne : 2 * b ≠ 0 := mul_ne_zero (by norm_num) (by
    intro h
    simp [h] at hb)
  apply mul_left_cancel₀ hbne
  rw [mul_inv_cancel_left₀ hbne]
  exact (sub_eq_zero.mp hzero).symm


theorem solution (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => regularizedMoment ħ m ε δ 2) (𝓝[>] 0)
      (𝓝 (ħ * ε * I / m * normalizingFactor ħ m ε)) := by
  let c : ℝ := m / (2 * ħ * ε)
  have hc : 0 < c := div_pos hm (mul_pos (mul_pos (by norm_num) hħ) hε)
  let b : ℝ → ℂ := fun δ => (c : ℂ) * ((δ : ℂ) - I) / ((1 + δ ^ 2 : ℝ) : ℂ)
  have hbpos (δ : ℝ) (hδ : 0 < δ) : 0 < (b δ).re := by
    simp only [b, Complex.div_ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.I_re, sub_zero, zero_mul, sub_zero]
    exact div_pos (mul_pos hc hδ) (by positivity)
  have hcoef (δ : ℝ) : -b δ = I * m / (2 * (ħ * (1 - I * δ)) * ε) := by
    have hd : (1 - I * (δ : ℂ)) ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp at hh
    have hs : (1 + δ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    dsimp [b, c]
    push_cast
    field_simp [hd, Complex.ofReal_ne_zero.mpr hħ.ne',
      Complex.ofReal_ne_zero.mpr hε.ne', Complex.ofReal_ne_zero.mpr hs]
    ring_nf
    have hsc : (1 + (δ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hs
    have hdc : (1 - (δ : ℂ) * I) ≠ 0 := by simpa [mul_comm] using hd
    field_simp [hsc, hdc]
    ring_nf
    simp [Complex.I_sq]
  have hmoment (δ : ℝ) (hδ : 0 < δ) : regularizedMoment ħ m ε δ 2 =
      (2 * b δ)⁻¹ * regularizedMoment ħ m ε δ 0 := by
    have htwo : regularizedMoment ħ m ε δ 2 =
        ∫ ξ : ℝ, (ξ : ℂ) ^ 2 * Complex.exp (-b δ * (ξ : ℂ) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      congr 2
      rw [hcoef]
      ring
    have hzero : regularizedMoment ħ m ε δ 0 =
        ∫ ξ : ℝ, Complex.exp (-b δ * (ξ : ℂ) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [pow_zero, one_mul]
      congr 1
      rw [hcoef]
      ring
    rw [htwo, hzero]
    exact gaussian_sq_integral (hbpos δ hδ)
  have hb0 : b 0 = -(c : ℂ) * I := by simp [b]
  have hbne : 2 * b 0 ≠ 0 := by
    rw [hb0]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hc.ne')) I_ne_zero)
  have hbcont : ContinuousAt b 0 := by
    dsimp [b]
    fun_prop (disch := norm_num)
  have hinv : (2 * b 0)⁻¹ = ħ * ε * I / m := by
    rw [hb0]
    dsimp [c]
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hclim : Tendsto (fun δ : ℝ => (2 * b δ)⁻¹) (𝓝[>] 0) (𝓝 (ħ * ε * I / m)) := by
    rw [← hinv]
    exact ((continuousAt_const.mul hbcont).inv₀ hbne).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hclim.mul (fresnel_zeroth_moment ħ m ε hħ hm hε)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hmoment δ hδ).symm
