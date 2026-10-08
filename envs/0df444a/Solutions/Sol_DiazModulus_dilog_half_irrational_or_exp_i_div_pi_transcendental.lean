-- Prove2me | solution 1 for DiazModulus.dilog_half_irrational_or_exp_i_div_pi_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-04T18:34:02.688495+00:00
-- url     : https://prove2.me/submissions/dba5c08c-103c-4b31-aab0-cc688189478e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_log_of_rational_quadratic_relation

open Complex ComplexConjugate

/-- If `π²/12 - (log 2)²/2 = s` is rational, then `-(1/2) (log 2)² + (1/12) π² = s`, and
`recip_pi_log_of_rational_quadratic_relation` applies to `t = log 2`, since `e^{log 2} = 2`. -/
theorem solution :
    Irrational (Real.pi ^ 2 / 12 - Real.log 2 ^ 2 / 2) ∨
      ∀ γ : ℚ, γ ≠ 0 →
        Transcendental ℚ (Complex.exp (Complex.I * (γ : ℂ) / ((Real.pi : ℝ) : ℂ))) := by
  by_cases h : Irrational (Real.pi ^ 2 / 12 - Real.log 2 ^ 2 / 2)
  · exact Or.inl h
  obtain ⟨s, hs⟩ := not_not.mp h
  refine Or.inr fun γ hγ => DiazModulus.recip_pi_log_of_rational_quadratic_relation (Real.log 2)
    (Real.log_pos one_lt_two).ne' ?_ (-1 / 2) (1 / 12) s (by norm_num) ?_ γ hγ
  · rw [← Complex.ofReal_exp, Real.exp_log two_pos]
    exact_mod_cast isAlgebraic_natCast (R := ℚ) (A := ℂ) 2
  · rw [hs]
    push_cast
    ring

#print axioms solution
