-- Prove2me | solution 1 for D1Bound5.bennettTwoNodes_injective
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:23.270121+00:00
-- url     : https://prove2.me/submissions/02c93c4b-1c30-4469-8f7a-321618ec35f7

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]

theorem _root_.solution (a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (bennettTwoNodes a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [bennettTwoNodes]





end D1Bound5
end
