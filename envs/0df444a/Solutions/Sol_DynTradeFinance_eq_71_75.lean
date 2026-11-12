-- Prove2me | solution 1 for DynTradeFinance.eq_71_75
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:17:35.842204+00:00
-- url     : https://prove2.me/submissions/5e64c28b-5684-454c-9b02-c42c5400a068

import Mathlib

theorem solution (p₁ l₁ l₂ μ δ dbar : ℝ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hl : l₁ < l₂)
    (hδ : 0 < δ) (hδμ : δ < μ) (hδ1 : δ < 1) (hdbar : 0 < dbar) :
    HasDerivAt (fun p : ℝ => -(p * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)))
      (-((l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) p₁ ∧
    -((l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)) < 0 ∧
    HasDerivAt (fun a : ℝ => -(p₁ * a * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)))
      (-(p₁ * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) (l₂ - l₁) ∧
    -(p₁ * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)) < 0 ∧
    HasDerivAt (fun m : ℝ => -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (m - δ) * dbar) ^ 2)))
      (p₁ * (l₂ - l₁) * (2 * δ * dbar) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3)) μ ∧
    0 < p₁ * (l₂ - l₁) * (2 * δ * dbar) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3) ∧
    HasDerivAt (fun s : ℝ => -(p₁ * (l₂ - l₁) * s / ((1 - s) * (1 + (μ - s) * dbar) ^ 2)))
      (-(p₁ * (l₂ - l₁) * ((1 - δ) * (1 + (μ - δ) * dbar) +
          δ * (1 + (μ - δ) * dbar + 2 * dbar * (1 - δ))) /
        ((1 - δ) ^ 2 * (1 + (μ - δ) * dbar) ^ 3))) δ ∧
    -(p₁ * (l₂ - l₁) * ((1 - δ) * (1 + (μ - δ) * dbar) +
          δ * (1 + (μ - δ) * dbar + 2 * dbar * (1 - δ))) /
        ((1 - δ) ^ 2 * (1 + (μ - δ) * dbar) ^ 3)) < 0 := by
  have hL : 0 < l₂ - l₁ := by linarith
  have h1d : 0 < 1 - δ := by linarith
  have hu : 0 < 1 + (μ - δ) * dbar := by
    have := mul_pos (sub_pos.mpr hδμ) hdbar
    linarith
  have hC : 0 < (1 - δ) * (1 + (μ - δ) * dbar) ^ 2 := mul_pos h1d (pow_pos hu 2)
  have hu0 := hu.ne'
  have h1d0 := h1d.ne'
  have d1 : HasDerivAt (fun p : ℝ => -(p * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)))
      (-((l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) p₁ := by
    have e : (fun p : ℝ => -(p * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) =
        fun p => p * (-((l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) := by
      funext p; ring
    rw [e]
    exact hasDerivAt_mul_const _
  have d3 : HasDerivAt (fun a : ℝ => -(p₁ * a * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)))
      (-(p₁ * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) (l₂ - l₁) := by
    have e : (fun a : ℝ => -(p₁ * a * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) =
        fun a => a * (-(p₁ * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) := by
      funext a; ring
    rw [e]
    exact hasDerivAt_mul_const _
  have d5 : HasDerivAt (fun m : ℝ => -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (m - δ) * dbar) ^ 2)))
      (p₁ * (l₂ - l₁) * (2 * δ * dbar) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3)) μ := by
    have hU : HasDerivAt (fun m : ℝ => 1 + (m - δ) * dbar) dbar μ :=
      ((((hasDerivAt_id' μ).sub_const δ).mul_const dbar).const_add 1).congr_deriv (by ring)
    have hD := (hU.fun_pow 2).const_mul (1 - δ)
    have h := ((hasDerivAt_const μ (p₁ * (l₂ - l₁) * δ)).div hD hC.ne').neg
    refine h.congr_deriv ?_
    field_simp <;> ring
  have d7 : HasDerivAt (fun s : ℝ => -(p₁ * (l₂ - l₁) * s / ((1 - s) * (1 + (μ - s) * dbar) ^ 2)))
      (-(p₁ * (l₂ - l₁) * ((1 - δ) * (1 + (μ - δ) * dbar) +
          δ * (1 + (μ - δ) * dbar + 2 * dbar * (1 - δ))) /
        ((1 - δ) ^ 2 * (1 + (μ - δ) * dbar) ^ 3))) δ := by
    have hU : HasDerivAt (fun s : ℝ => 1 + (μ - s) * dbar) (-dbar) δ :=
      ((((hasDerivAt_id' δ).const_sub μ).mul_const dbar).const_add 1).congr_deriv (by ring)
    have hD := ((hasDerivAt_id' δ).const_sub 1).fun_mul (hU.fun_pow 2)
    have hN := (hasDerivAt_id' δ).const_mul (p₁ * (l₂ - l₁))
    have h := (hN.div hD hC.ne').neg
    refine h.congr_deriv ?_
    field_simp <;> ring
  refine ⟨d1, ?_, d3, ?_, d5, ?_, d7, ?_⟩
  · exact neg_neg_of_pos (div_pos (mul_pos hL hδ) hC)
  · exact neg_neg_of_pos (div_pos (mul_pos hp₁ hδ) hC)
  · exact div_pos (mul_pos (mul_pos hp₁ hL) (mul_pos (mul_pos two_pos hδ) hdbar))
      (mul_pos h1d (pow_pos hu 3))
  · apply neg_neg_of_pos
    apply div_pos _ (mul_pos (pow_pos h1d 2) (pow_pos hu 3))
    apply mul_pos (mul_pos hp₁ hL)
    have := mul_pos h1d hu
    have := mul_pos (mul_pos two_pos hdbar) h1d
    nlinarith
