-- Prove2me | solution 1 for D1Bound5.bennettClearedMatrix_det_constant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:32.329621+00:00
-- url     : https://prove2.me/submissions/cbc4a6bf-16a7-4619-b1ed-6e639f10931d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantConstant_Definitions
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions
import Theorems.Thm_D1Bound5_bennettClearedMatrix_det_eval_of_ne_zero

section
open Finset

namespace D1Bound5

variable {F I : Type*} [Field F] [CharZero F]
variable [Fintype I] [DecidableEq I]







/-- The cleared determinant is a constant polynomial. Consequently evaluation
at a removed node, including zero, is justified algebraically. -/
theorem _root_.solution
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (q : I) (hq : a q = 0) :
    (bennettClearedMatrix a k ν).det =
      Polynomial.C ((bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite {N : F | N ≠ 0} := by
    have hset : {N : F | N ≠ 0} = Set.univ \ {0} := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
        true_and]
    rw [hset]
    exact (Set.infinite_univ : Set.Infinite (Set.univ : Set F)).sdiff
      (Set.finite_singleton (0 : F))
  apply hinf.mono
  intro N hN
  simpa only [Set.mem_setOf_eq, Polynomial.eval_C] using
    bennettClearedMatrix_det_eval_of_ne_zero a ha k hk ν q hq N hN



end D1Bound5
end
