-- Prove2me | solution 2 for DiazModulus.generic_conj_pair_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:37:00.519687+00:00
-- url     : https://prove2.me/submissions/faa2711e-6299-43f8-9e37-5f0df9fc3291

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_generic_conj_pair_no_quadratic_relation
import Theorems.Thm_DiazModulus_four_exp_barrier_of_no_quadratic_relation

open Complex ComplexConjugate

/- The entries of `M` are rational linear forms in `u, ū, πi`, and these satisfy no rational
quadratic relation (`generic_conj_pair_no_quadratic_relation`), so
`four_exp_barrier_of_no_quadratic_relation` applies. -/
open DiazModulus in
theorem solution (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  exact four_exp_barrier_of_no_quadratic_relation _
    (fun F hF => generic_conj_pair_no_quadratic_relation u hu hρ hgen F hF) A M hM hdet

#print axioms solution
