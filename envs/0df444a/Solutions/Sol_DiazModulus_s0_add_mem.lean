-- Prove2me | solution 1 for DiazModulus.s0_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:08:12.766101+00:00
-- url     : https://prove2.me/submissions/26b82825-25f2-4b76-9787-06b596c47e6b

import Mathlib

theorem solution :
    ∀ γ₁ γ₂ : ℂ, IsAlgebraic ℚ γ₁ →
      IsAlgebraic ℚ (Complex.exp (γ₁ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ γ₂ →
      IsAlgebraic ℚ (Complex.exp (γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (γ₁ + γ₂) ∧
        IsAlgebraic ℚ (Complex.exp ((γ₁ + γ₂) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ₁ γ₂ h1 he1 h2 he2
  refine ⟨h1.add h2, ?_⟩
  rw [add_div, Complex.exp_add]
  exact he1.mul he2
