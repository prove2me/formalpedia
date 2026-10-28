-- Prove2me | solution 1 for D1Bound5.bennettClearedResidue_offDiagonal_at_node
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:50.806983+00:00
-- url     : https://prove2.me/submissions/cb241bc6-114d-40de-9d8f-c949109c4ada

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]









section Nodes

variable {I : Type*} [DecidableEq I]











/-- At N=-a_j the off-diagonal part of column j vanishes identically. -/
theorem _root_.solution
    (s : Finset I) (a : I → F) (k : ℕ) (hk : 1 ≤ k) (ν : F)
    (i j : I) (hij : i ≠ j) :
    (bennettClearedResidue s a k ν i j).eval (-a j) = 0 := by
  simp only [bennettClearedResidue, if_neg hij, add_zero,
    bennettClearedTaylor, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro ht hht
  have hsum := Finset.mem_antidiagonal.mp hht
  have hp : 0 < k - ht.1 := by omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, neg_add_cancel,
    zero_pow (Nat.ne_of_gt hp), mul_zero]





end Nodes

end D1Bound5
end
