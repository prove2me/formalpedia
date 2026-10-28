-- Prove2me | solution 1 for CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:43:55.574536+00:00
-- url     : https://prove2.me/submissions/ab2664af-aa4a-4d26-a9aa-b532ddfb9d44

import Mathlib.Algebra.MvPolynomial.PDeriv

namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
set_option autoImplicit false

/-!
Formal polynomial calculus for moving derivatives before linear substitutions.
These identities do not assert Lorentzianity or a signature bound.
-/

namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LinearPolynomialChainRule

open scoped BigOperators

/-- INTERNAL: The chain rule for a linear substitution, in the exact algebraic
form needed to normalize a descendant derivation.
TEXLINE: main.tex:326-348 -/
theorem solution {σ τ : Type} [Fintype σ] [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (t : τ) :
    MvPolynomial.pderiv t
      (MvPolynomial.aeval (fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u) p) =
    MvPolynomial.aeval (fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u)
      (∑ s, MvPolynomial.C (a s t) * MvPolynomial.pderiv s p) := by
  classical
  let L := fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u
  have hL (s : σ) : MvPolynomial.pderiv t (L s) = MvPolynomial.C (a s t) := by
    simp [L, MvPolynomial.pderiv_X, Pi.single_apply]
  change MvPolynomial.pderiv t (MvPolynomial.aeval L p) =
    MvPolynomial.aeval L (∑ s, MvPolynomial.C (a s t) * MvPolynomial.pderiv s p)
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp, hL,
      MvPolynomial.pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    simp only [Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro s _
      rw [MvPolynomial.aeval_X]
      exact mul_assoc _ _ _
    · simp [mul_comm]
