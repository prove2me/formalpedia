-- Prove2me | solution 1 for DerivativeChainPrivate.row_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:46:01.548922+00:00
-- url     : https://prove2.me/submissions/87938f23-3fbd-491a-8ba1-f4efce32247b

import Definitions.Def_DerivativeChainPrivate_foundations
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

/-!
# Exact derivative-row definitions and structural adapters

The four definitions below reproduce the definitions in the private mission
statement. No statement draft is imported. Rows are the actual, unnormalized
iterated derivatives: only the original row is asserted to be monic.
-/

open scoped BigOperators

namespace DerivativeChainPrivate

















/-- Root slots, including repetitions, contribute exactly one degree each. -/
@[simp] theorem fromRoots_natDegree {n : ℕ} (a : Fin n → ℂ) :
    (fromRoots a).natDegree = n := by
  unfold fromRoots
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp













end DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) :
    (row a m).natDegree = m := by
  have hiter : ∀ k : ℕ,
      ((Polynomial.derivative^[k]) (fromRoots a)).natDegree = n - k := by
    intro k
    induction k with
    | zero => exact fromRoots_natDegree a
    | succ k ih =>
      rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
      omega
  unfold row
  rw [hiter]
  omega
