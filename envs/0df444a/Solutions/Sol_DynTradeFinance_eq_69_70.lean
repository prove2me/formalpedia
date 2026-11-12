-- Prove2me | solution 1 for DynTradeFinance.eq_69_70
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:35:39.170104+00:00
-- url     : https://prove2.me/submissions/b6391eef-d9b8-403c-828d-f8a06fc28bdb

import Mathlib
import Definitions.Def_DynTradeFinance_ValueOfDTF

open DynTradeFinance in
theorem solution (p₁ l₁ l₂ μ δ dbar : ℝ) (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hl : l₁ < l₂)
    (hδ : 0 < δ) (hδμ : δ < μ) (hδ1 : δ < 1) (hdbar : 0 < dbar) :
    valueFormula p₁ l₁ l₂ μ (1 / dbar) δ =
      p₁ * (l₂ - l₁) * (δ / ((1 - δ) * (μ - δ))) * (1 / (1 + (μ - δ) * dbar)) ∧
    HasDerivAt (fun x : ℝ => p₁ * (l₂ - l₁) * (δ / ((1 - δ) * (μ - δ))) * (1 / (1 + (μ - δ) * x)))
      (-(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2))) dbar ∧
    -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2)) < 0 ∧
    HasDerivAt (fun x : ℝ => -(p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * x) ^ 2)))
      (p₁ * (l₂ - l₁) * (2 * δ * (μ - δ)) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3)) dbar ∧
    0 < p₁ * (l₂ - l₁) * (2 * δ * (μ - δ)) / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 3) := by
  have hl' : 0 < l₂ - l₁ := sub_pos.2 hl
  have ha : 0 < μ - δ := sub_pos.2 hδμ
  have h1δ : 0 < 1 - δ := sub_pos.2 hδ1
  have hA : 0 < 1 + (μ - δ) * dbar := by nlinarith
  have hdne : dbar ≠ 0 := hdbar.ne'
  have hane : μ - δ ≠ 0 := ha.ne'
  have h1δne : 1 - δ ≠ 0 := h1δ.ne'
  have hAne : 1 + (μ - δ) * dbar ≠ 0 := hA.ne'
  have hlin : HasDerivAt (fun x : ℝ => 1 + (μ - δ) * x) ((μ - δ) * 1) dbar :=
    ((hasDerivAt_id dbar).const_mul (μ - δ)).const_add 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold valueFormula
    congr 1
    have h1 : 1 / dbar + μ - δ ≠ 0 := by
      have : 0 < 1 / dbar := by positivity
      linarith
    rw [div_eq_div_iff h1 hAne]
    have hc : 1 / dbar * dbar = 1 := one_div_mul_cancel hdne
    linear_combination (μ - δ) * hc
  · have h := ((hasDerivAt_const dbar (1:ℝ)).fun_div hlin hAne).const_mul
      (p₁ * (l₂ - l₁) * (δ / ((1 - δ) * (μ - δ))))
    refine h.congr_deriv ?_
    field_simp <;> ring
  · have : 0 < p₁ * (l₂ - l₁) * δ / ((1 - δ) * (1 + (μ - δ) * dbar) ^ 2) :=
      div_pos (mul_pos (mul_pos hp₁ hl') hδ) (mul_pos h1δ (pow_pos hA 2))
    linarith
  · have hg : HasDerivAt (fun x : ℝ => (1 - δ) * (1 + (μ - δ) * x) ^ 2)
        ((1 - δ) * (2 * (1 + (μ - δ) * dbar) * (μ - δ))) dbar :=
      ((hlin.fun_pow 2).const_mul (1 - δ)).congr_deriv (by norm_num <;> ring)
    have hgne : (1 - δ) * (1 + (μ - δ) * dbar) ^ 2 ≠ 0 := (mul_pos h1δ (pow_pos hA 2)).ne'
    have h := ((hasDerivAt_const dbar (p₁ * (l₂ - l₁) * δ)).fun_div hg hgne).fun_neg
    refine h.congr_deriv ?_
    field_simp <;> ring
  · exact div_pos (mul_pos (mul_pos hp₁ hl') (by positivity)) (mul_pos h1δ (pow_pos hA 3))
