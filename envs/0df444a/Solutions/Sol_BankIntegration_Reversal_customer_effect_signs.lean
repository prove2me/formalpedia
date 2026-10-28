-- Prove2me | solution 1 for BankIntegration.Reversal.customer_effect_signs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:25:16.554834+00:00
-- url     : https://prove2.me/submissions/a41d9256-c265-4863-a83f-9e6a8e2c7971

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model

open BankIntegration.Reversal in
theorem solution (lam a1 a2 b1 b2 : ℝ) (n : ℕ)
    (hS : Standing lam a1 a2 b1 b2 n) (hξ : xi a1 b1 < xi a2 b2) :
    xi a1 b1 < xiStar a1 a2 b1 b2 ∧ xiStar a1 a2 b1 b2 < xi a2 b2 ∧
      bankCustomerEffect lam n (xi a2 b2) (xiStar a1 a2 b1 b2) < 0 ∧
      0 < bankCustomerEffect lam n (xi a1 b1) (xiStar a1 a2 b1 b2) := by
  obtain ⟨hlam, ha1, ha2, hb1, hb2, hn⟩ := hS
  unfold xi at hξ
  rw [div_lt_div_iff₀ ha1 ha2] at hξ
  have h1 : xi a1 b1 < xiStar a1 a2 b1 b2 := by
    unfold xi xiStar
    rw [div_lt_div_iff₀ ha1 (by positivity)]
    nlinarith
  have h2 : xiStar a1 a2 b1 b2 < xi a2 b2 := by
    unfold xi xiStar
    rw [div_lt_div_iff₀ (by positivity) ha2]
    nlinarith
  have hx1 : 0 < xi a1 b1 := by unfold xi; positivity
  have hxs : 0 < xiStar a1 a2 b1 b2 := by unfold xiStar; positivity
  have hx2 : 0 < xi a2 b2 := by unfold xi; positivity
  have hc : 0 < lam * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    have : 0 < lam := by linarith
    positivity
  refine ⟨h1, h2, ?_, ?_⟩
  · unfold bankCustomerEffect
    have : 1 / (1 + xi a2 b2) < 1 / (1 + xiStar a1 a2 b1 b2) :=
      one_div_lt_one_div_of_lt (by linarith) (by linarith)
    have := mul_pos hc (sub_pos.mpr this)
    nlinarith
  · unfold bankCustomerEffect
    have : 1 / (1 + xiStar a1 a2 b1 b2) < 1 / (1 + xi a1 b1) :=
      one_div_lt_one_div_of_lt (by linarith) (by linarith)
    exact mul_pos hc (sub_pos.mpr this)
