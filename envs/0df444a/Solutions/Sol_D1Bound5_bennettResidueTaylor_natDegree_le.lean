-- Prove2me | solution 1 for D1Bound5.bennettResidueTaylor_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:11.874971+00:00
-- url     : https://prove2.me/submissions/ff71b184-416c-4b1f-872f-72119b59166b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



theorem _root_.solution (k r : ℕ) (hr : r ≤ k)
    (ν a : F) (B : PowerSeries F) :
    (bennettResidueTaylor k r ν a B).natDegree ≤ k := by
  have hlin : (1 + Polynomial.C a * Polynomial.X : Polynomial F).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  unfold bennettResidueTaylor
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ht hht
  have hsum := Finset.mem_antidiagonal.mp hht
  have hh : ht.1 ≤ k := by omega
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_mul_le.trans
  have hpow : ((1 + Polynomial.C a * Polynomial.X : Polynomial F) ^
      (k - ht.1)).natDegree ≤ k - ht.1 := by
    simpa using Polynomial.natDegree_pow_le_of_le (k - ht.1) hlin
  calc
    (Polynomial.X ^ ht.1 : Polynomial F).natDegree +
        ((1 + Polynomial.C a * Polynomial.X : Polynomial F) ^
          (k - ht.1)).natDegree ≤ ht.1 + (k - ht.1) := by
      exact add_le_add (by simp) hpow
    _ = k := Nat.add_sub_of_le hh





section Nodes

variable {I : Type*} [DecidableEq I]







end Nodes

end D1Bound5
end
