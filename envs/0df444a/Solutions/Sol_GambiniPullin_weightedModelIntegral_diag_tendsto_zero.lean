-- Prove2me | solution 1 for GambiniPullin.weightedModelIntegral_diag_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:24:37.92466+00:00
-- url     : https://prove2.me/submissions/1876ce8f-ba65-4119-b2a8-1a7d4c3cad5f

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

set_option autoImplicit false

open MeasureTheory GambiniPullin in
lemma gp_abs_integrand_le (α β σ x y : ℝ) (hα : 0 ≤ α) (hβ : 0 < β) (hσ : 0 ≤ σ) :
    |weightedModelIntegrand α β σ x y| ≤
      2 / β * (Real.exp (-(β / 2) * x ^ 2) * Real.exp (-(β / 2) * y ^ 2)) := by
  have hden : 1 ≤ modelDenom σ x y := by
    unfold modelDenom
    have h1 : 0 < 1 + σ * y ^ 2 := by nlinarith [mul_nonneg hσ (sq_nonneg y)]
    have h2 : 0 ≤ y ^ 2 / (1 + σ * y ^ 2) := div_nonneg (sq_nonneg y) h1.le
    nlinarith [sq_nonneg x]
  have hM : |modelIntegrand σ x y| ≤ x ^ 2 + y ^ 2 := by
    unfold modelIntegrand
    rw [abs_div, abs_of_pos (pow_pos (by linarith : (0:ℝ) < modelDenom σ x y) 2)]
    calc |x ^ 2 - y ^ 2| / modelDenom σ x y ^ 2 ≤ |x ^ 2 - y ^ 2| :=
          div_le_self (abs_nonneg _) (one_le_pow₀ hden)
      _ ≤ x ^ 2 + y ^ 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have hA : Real.exp (-α * x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hα (sq_nonneg x)])
  set t := x ^ 2 + y ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hsplit : Real.exp (-(β / 2) * x ^ 2) * Real.exp (-(β / 2) * y ^ 2)
      = Real.exp (-(β / 2) * t) := by
    rw [← Real.exp_add, ht]; ring_nf
  rw [hsplit]
  set E := Real.exp (-(β / 2) * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 : Real.exp (-β * t) = E * E := by
    rw [hE, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (β / 2 * t) * E = 1 := by
    rw [hE, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h3 : β / 2 * t + 1 ≤ Real.exp (β / 2 * t) := Real.add_one_le_exp _
  have h4 : β / 2 * t * E ≤ 1 := by nlinarith
  have hkey : t * Real.exp (-β * t) ≤ 2 / β * E := by
    rw [e1, div_mul_eq_mul_div, le_div_iff₀ hβ]
    nlinarith [mul_le_mul_of_nonneg_right h4 hE0.le]
  unfold weightedModelIntegrand
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-α * x ^ 2) * Real.exp (-β * t) * |modelIntegrand σ x y|
      ≤ 1 * Real.exp (-β * t) * t := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le) hM
          (abs_nonneg _) (by positivity)
    _ = t * Real.exp (-β * t) := by ring
    _ ≤ 2 / β * E := hkey

open MeasureTheory Filter GambiniPullin in
lemma gp_abs_weighted_le (α β σ : ℝ) (hα : 0 ≤ α) (hβ : 0 < β) (hσ : 0 ≤ σ) :
    |weightedModelIntegral α β σ| ≤ 4 * Real.pi / β ^ 2 := by
  have hb : 0 < β / 2 := by linarith
  have hgint : Integrable (fun p : ℝ × ℝ =>
      2 / β * (Real.exp (-(β / 2) * p.1 ^ 2) * Real.exp (-(β / 2) * p.2 ^ 2))) := by
    have := Integrable.mul_prod (integrable_exp_neg_mul_sq hb) (integrable_exp_neg_mul_sq hb)
    rw [Measure.volume_eq_prod]
    exact this.const_mul _
  have hval : ∫ p : ℝ × ℝ,
      2 / β * (Real.exp (-(β / 2) * p.1 ^ 2) * Real.exp (-(β / 2) * p.2 ^ 2))
        = 4 * Real.pi / β ^ 2 := by
    rw [integral_const_mul, Measure.volume_eq_prod,
      integral_prod_mul (fun x : ℝ => Real.exp (-(β / 2) * x ^ 2))
        (fun x : ℝ => Real.exp (-(β / 2) * x ^ 2)),
      integral_gaussian, Real.mul_self_sqrt (by positivity)]
    field_simp
    ring
  unfold weightedModelIntegral
  rw [← hval, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hgint ?_
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs]
    exact gp_abs_integrand_le α β σ p.1 p.2 hα hβ hσ)

open MeasureTheory Filter GambiniPullin in
theorem solution (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun β => weightedModelIntegral β β σ) atTop (nhds 0) := by
  have hlim : Tendsto (fun β : ℝ => 4 * Real.pi / β ^ 2) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop (α := ℝ) (two_ne_zero)).inv_tendsto_atTop
    have h2 := h.const_mul (4 * Real.pi)
    rw [mul_zero] at h2
    refine h2.congr' (Filter.Eventually.of_forall fun β => ?_)
    simp [div_eq_mul_inv]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun β => abs_nonneg _) ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
  exact gp_abs_weighted_le β β σ hβ.le hβ hσ.le
