-- Prove2me | solution 1 for CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:55.342776+00:00
-- url     : https://prove2.me/submissions/b7a6d082-25d1-4d5d-9233-9bf5461916d8

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

/-- INTERNAL: Consecutive linear substitutions compose by matrix multiplication.
TEXLINE: main.tex:326-348 -/
theorem solution {σ τ υ : Type} [Fintype τ] [Fintype υ]
    (a : σ → τ → ℚ) (b : τ → υ → ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.aeval (fun t => ∑ u, MvPolynomial.C (b t u) * MvPolynomial.X u)
      (MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p) =
    MvPolynomial.aeval
      (fun s => ∑ u, MvPolynomial.C (∑ t, a s t * b t u) * MvPolynomial.X u) p := by
  rw [MvPolynomial.comp_aeval_apply]
  suffices h : (fun s =>
      MvPolynomial.aeval (fun t => ∑ u, MvPolynomial.C (b t u) * MvPolynomial.X u)
        (∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t)) =
      (fun s => ∑ u, MvPolynomial.C (∑ t, a s t * b t u) * MvPolynomial.X u) by
    rw [h]
  funext s
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Finset.mul_sum, map_sum, Finset.sum_mul,
    map_mul, mul_assoc]
  exact Finset.sum_comm
