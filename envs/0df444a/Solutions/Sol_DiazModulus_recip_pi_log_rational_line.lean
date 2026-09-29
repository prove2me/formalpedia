-- Prove2me | solution 1 for DiazModulus.recip_pi_log_rational_line
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T16:03:57.033764+00:00
-- url     : https://prove2.me/submissions/6655a686-4f5f-4b62-bfa0-0b357ddb2377

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_gelfond_schneider

open Complex ComplexConjugate

/-- Two exceptions to `(S)` are rationally proportional. With `λⱼ = γⱼ/(πi)` in `ℒ`, the ratio
`λ₁/λ₂ = γ₁/γ₂` is algebraic, so Gelfond–Schneider forces it to be rational. -/
theorem solution :
    ∀ γ₁ γ₂ : ℂ, IsAlgebraic ℚ γ₁ → IsAlgebraic ℚ γ₂ → γ₂ ≠ 0 →
      IsAlgebraic ℚ (Complex.exp (γ₁ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (Complex.exp (γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      ∃ q : ℚ, γ₁ = (q : ℂ) * γ₂ := by
  intro γ₁ γ₂ h1 h2 h20 he1 he2
  by_contra hne
  simp only [not_exists] at hne
  have hpiI : (((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hb : IsAlgebraic ℚ (γ₁ / γ₂) := by
    rw [← DiazModulus.mem_Qbar_iff] at h1 h2 ⊢
    exact Subfield.div_mem _ h1 h2
  have hbq : ∀ q : ℚ, γ₁ / γ₂ ≠ (q : ℂ) := by
    intro q hq
    exact hne q (by rw [← hq]; field_simp)
  have hl0 : γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 := div_ne_zero h20 hpiI
  have hGS := Schanuel.gelfond_schneider (γ₁ / γ₂) (γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I))
    hb hbq he2 hl0
  have hprod : γ₁ / γ₂ * (γ₂ / (((Real.pi : ℝ) : ℂ) * Complex.I))
      = γ₁ / (((Real.pi : ℝ) : ℂ) * Complex.I) := by
    field_simp
  rw [hprod] at hGS
  exact hGS he1

#print axioms solution
