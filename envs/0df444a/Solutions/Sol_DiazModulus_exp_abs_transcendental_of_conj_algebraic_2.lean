-- Prove2me | solution 2 for DiazModulus.exp_abs_transcendental_of_conj_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:18:55.833005+00:00
-- url     : https://prove2.me/submissions/5f4b5ead-9673-4ae6-9fd8-923f46ba4353

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_exp_abs_transcendental_of_isAlgebraic_adjoin

open Complex ComplexConjugate

namespace S7W1_exp_abs_conj_algebraic

/-- Every `x` is algebraic over `ℚ[x]`: it is the image of the generator of `ℚ[x]`. -/
theorem self_isAlgebraic (x : ℂ) : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) x :=
  isAlgebraic_algebraMap (⟨x, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin ℚ ({x} : Set ℂ)))

end S7W1_exp_abs_conj_algebraic

open S7W1_exp_abs_conj_algebraic in
theorem solution (lam : ℂ)
    (hlam : IsAlgebraic ℚ (Complex.exp lam)) (him : lam.im ≠ 0)
    (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({lam} : Set ℂ))) (conj lam)) :
    Transcendental ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ)) := by
  -- The node with `x := λ`: `λ` is algebraic over `ℚ[λ]`, and `λ̄` is by hypothesis.
  exact DiazModulus.exp_abs_transcendental_of_isAlgebraic_adjoin lam lam hlam him
    (self_isAlgebraic lam) hdep

#print axioms solution
