-- Prove2me | solution 1 for Diaz.two_failures_give_algebraic_log_product
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:01:35.149064+00:00
-- url     : https://prove2.me/submissions/cf34d064-88f2-47a4-a887-f5a4e709a7f4

import Mathlib

open ComplexConjugate

theorem solution {t₁ t₂ : ℝ}
    (e₁ : IsAlgebraic ℚ ((Real.exp t₁ : ℝ) : ℂ)) (e₂ : IsAlgebraic ℚ ((Real.exp t₂ : ℝ) : ℂ))
    (h₁ : IsAlgebraic ℚ ((t₁ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ))
    (h₂ : IsAlgebraic ℚ ((t₂ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ)) :
    IsAlgebraic ℚ ((Real.exp (t₁ + t₂) : ℝ) : ℂ)
      ∧ IsAlgebraic ℚ ((Real.exp (t₁ - t₂) : ℝ) : ℂ)
      ∧ IsAlgebraic ℚ (((t₁ + t₂) * (t₁ - t₂) : ℝ) : ℂ)
      ∧ (t₁ ^ 2 ≠ t₂ ^ 2 → ((t₁ + t₂) * (t₁ - t₂) : ℝ) ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.exp_add, Complex.ofReal_mul]
    exact e₁.mul e₂
  · rw [Real.exp_sub, Complex.ofReal_div, div_eq_mul_inv]
    exact e₁.mul e₂.inv
  · have hrw : (((t₁ + t₂) * (t₁ - t₂) : ℝ) : ℂ)
        = ((t₁ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) - ((t₂ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub]
      congr 1
      ring
    rw [hrw]
    exact h₁.sub h₂
  · intro hne hzero
    apply hne
    nlinarith [hzero]
