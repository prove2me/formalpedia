-- Prove2me | solution 1 for D1Bound5.bennettDirectedProduct_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:41.662989+00:00
-- url     : https://prove2.me/submissions/5a3a0bc2-45d0-4723-b0a1-3653aa1320ac

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



/-- Distinct nodes make every directed reciprocal-difference factor nonzero. -/
theorem _root_.solution {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → F) (ha : Function.Injective a) (k : ℕ) :
    bennettDirectedProduct a k ≠ 0 := by
  unfold bennettDirectedProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply pow_ne_zero
  apply inv_ne_zero
  exact sub_ne_zero.mpr (ha.ne (Finset.mem_erase.mp hj).1.symm)





end D1Bound5
end
