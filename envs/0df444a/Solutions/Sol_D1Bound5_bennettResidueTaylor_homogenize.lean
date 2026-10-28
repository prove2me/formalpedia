-- Prove2me | solution 1 for D1Bound5.bennettResidueTaylor_homogenize
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:06.713249+00:00
-- url     : https://prove2.me/submissions/db7c9016-d79d-4edf-95a8-8447cb04565a

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions
import Theorems.Thm_D1Bound5_bennettHomogenizationTerm

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]







/-- Clearing the common N denominator recovers the polynomial G used in
the node-removal determinant induction. -/
theorem _root_.solution (k r : ℕ) (hr : r ≤ k)
    (ν a N : F) (B : PowerSeries F) (hN : N ≠ 0) :
    N ^ k * (bennettResidueTaylor k r ν a B).eval N⁻¹ =
      (bennettClearedTaylor k r ν a B).eval N := by
  unfold bennettResidueTaylor bennettClearedTaylor
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ht hht
  have hsum := Finset.mem_antidiagonal.mp hht
  have hh : ht.1 ≤ k := by omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  calc
    _ = (Ring.choose ((k : F) + ν) ht.1 * PowerSeries.coeff ht.2 B) *
        (N ^ k * ((N⁻¹) ^ ht.1 * (1 + a * N⁻¹) ^ (k - ht.1))) := by ring
    _ = _ := by rw [bennettHomogenizationTerm k ht.1 hh a N hN]

section Nodes

variable {I : Type*} [DecidableEq I]







end Nodes

end D1Bound5
end
