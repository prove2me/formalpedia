-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.sum_single_X
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T16:45:13.074692+00:00
-- url     : https://prove2.me/submissions/e3dc0511-a4e0-4e9b-b7a6-ecbdb86a65cd

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Complex.Basic

open Finset MvPolynomial

-- Exact statement from public theorem 66513045-fe5e-4a55-a491-1b264499aee2.
-- The public preamble's custom imports and unused namespace opens are omitted
-- in this standalone verification file; the theorem depends only on Mathlib.
theorem solution (c : Fin 84) :
    ∑ i : Fin 84, ((if i = c then (1 : ℝ) else 0 : ℝ) : ℂ) • (X i : MvPolynomial (Fin 84) ℂ)
      = X c := by
  classical
  rw [Finset.sum_eq_single c]
  · simp
  · intro i _ hic
    simp [hic]
  · intro hc
    exact (hc (Finset.mem_univ c)).elim

#print axioms solution
