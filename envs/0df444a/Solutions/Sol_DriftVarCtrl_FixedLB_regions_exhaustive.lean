-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.regions_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:58:53.339745+00:00
-- url     : https://prove2.me/submissions/51d58a6e-fd6b-4f72-996c-c44c3cc78e85

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
set_option autoImplicit false

open DriftVarCtrl.FixedLB

theorem solution (p : Params) (hv : v p .one < v p .two) :
    cond7 p ∨ cond8 p ∨ cond9 p ∨ cond10 p := by
  have hv1 : 0 < v p .one := by
    show 0 < 2 * p.μ₁ / p.σ₁ ^ 2
    have := p.hμ₁; have := p.hσ₁; positivity
  have hv2 : 0 < v p .two := lt_trans hv1 hv
  have hU := p.hU
  have hE1 : Real.exp (-v p .one * p.U) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith)
  have hE2 : Real.exp (-v p .two * p.U) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith)
  have hE1p : 0 < Real.exp (-v p .one * p.U) := Real.exp_pos _
  have hE2p : 0 < Real.exp (-v p .two * p.U) := Real.exp_pos _
  have hc : 0 < p.σ₂ ^ 2 / p.σ₁ ^ 2 := by have := p.hσ₁; have := p.hσ₂; positivity
  have hb : 0 < p.σ₁ ^ 2 / p.σ₂ ^ 2 := by have := p.hσ₁; have := p.hσ₂; positivity
  have ha : 0 < p.μ₁ / p.μ₂ := by have := p.hμ₁; have := p.hμ₂; positivity
  have h1 : dL1 p ≤ dU1 p := by
    unfold dL1 dU1
    have e : p.U / (1 - Real.exp (-v p .one * p.U)) - p.U * Real.exp (-v p .one * p.U) / (1 - Real.exp (-v p .one * p.U)) = p.U := by
      have hd : 1 - Real.exp (-v p .one * p.U) ≠ 0 := by linarith
      rw [← sub_div, show p.U - p.U * Real.exp (-v p .one * p.U) = p.U * (1 - Real.exp (-v p .one * p.U)) by ring, mul_div_assoc, div_self hd, mul_one]
    have : 0 ≤ (p.σ₂ ^ 2 / p.σ₁ ^ 2) * (v p .two - v p .one) * p.U := by
      have : 0 ≤ v p .two - v p .one := by linarith
      positivity
    nlinarith [e]
  have h2 : dL2 p ≤ dU2 p := by
    unfold dL2 dU2
    have hd : 0 < 1 - Real.exp (-v p .two * p.U) := by linarith
    have t1 : 0 ≤ p.σ₁ ^ 2 / p.σ₂ ^ 2 * (v p .two - v p .one) := by
      have : 0 ≤ v p .two - v p .one := by linarith
      positivity
    have t2 : p.U * Real.exp (-v p .two * p.U) / (1 - Real.exp (-v p .two * p.U)) ≤ p.U / (1 - Real.exp (-v p .two * p.U)) := by
      apply div_le_div_of_nonneg_right _ hd.le
      nlinarith
    have t3 : 0 ≤ p.U * Real.exp (-v p .two * p.U) / (1 - Real.exp (-v p .two * p.U)) := by positivity
    apply one_div_le_one_div_of_le
    · nlinarith [mul_nonneg t1 t3]
    · nlinarith [mul_le_mul_of_nonneg_left t2 t1]
  unfold cond7 cond8 cond9 cond10
  set x := Δh p .two
  set y := Δh p .one
  rcases lt_trichotomy y 0 with hy | hy | hy
  · -- y < 0
    by_cases hx1 : max (dL1 p * y) (dU1 p * y) ≤ x
    · exact Or.inl hx1
    by_cases hx2 : x ≤ min (dL2 p * y) (dU2 p * y)
    · exact Or.inr (Or.inl hx2)
    right; right; right
    push_neg at hx1 hx2
    have a1 : dU1 p * y ≤ dL1 p * y := by nlinarith
    have a2 : dU2 p * y ≤ dL2 p * y := by nlinarith
    rw [max_eq_left a1] at hx1
    rw [min_eq_right a2] at hx2
    exact ⟨⟨hx2, hx1⟩, hy⟩
  · rw [hy]
    simp only [mul_zero]
    rcases le_total 0 x with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl (by simpa using h))
  · by_cases hx1 : max (dL1 p * y) (dU1 p * y) ≤ x
    · exact Or.inl hx1
    by_cases hx2 : x ≤ min (dL2 p * y) (dU2 p * y)
    · exact Or.inr (Or.inl hx2)
    right; right; left
    push_neg at hx1 hx2
    have a1 : dL1 p * y ≤ dU1 p * y := by nlinarith
    have a2 : dL2 p * y ≤ dU2 p * y := by nlinarith
    rw [max_eq_right a1] at hx1
    rw [min_eq_left a2] at hx2
    exact ⟨⟨hx2, hx1⟩, hy⟩
