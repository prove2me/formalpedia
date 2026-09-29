-- Prove2me | solution 1 for DiazModulus.recip_pi_not_log_real_or_imag
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:22:05.271679+00:00
-- url     : https://prove2.me/submissions/a59889f9-2539-41f1-92e0-46ad541cf672

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_log_rational_line

open Complex ComplexConjugate

/-- At least one half of `(S)` holds. If both failed, a real exception and a purely imaginary
one would be rationally proportional by the rational-line theorem, so the real one would be
purely imaginary as well, hence zero. -/
theorem solution :
    (∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) ∨
    (∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.re = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) := by
  by_contra h
  simp only [not_or, not_forall, not_not, exists_prop] at h
  obtain ⟨⟨γ₁, a₁, n₁, i₁, e₁⟩, ⟨γ₂, a₂, n₂, r₂, e₂⟩⟩ := h
  obtain ⟨q, hq⟩ := DiazModulus.recip_pi_log_rational_line γ₁ γ₂ a₁ a₂ n₂ e₁ e₂
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  simp only [Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    zero_mul, sub_zero, add_zero, r₂, mul_zero] at hre him
  exact n₁ (Complex.ext (by simpa using hre) (by simpa using i₁))

#print axioms solution
