-- Prove2me | solution 1 for D1Bound5.finiteMNodes_injective
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:30.120396+00:00
-- url     : https://prove2.me/submissions/b74dd1e5-9cce-4e05-8d4d-e8120213b3f9

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions

section
open Finset Polynomial

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]













theorem _root_.solution (a b s : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) :
    Function.Injective (finiteMNodes a b s) := by
  have h01 : b*s ≠ 0 := mul_ne_zero hb hs
  have h02 : a*s ≠ 0 := mul_ne_zero ha hs
  have h03 : a*b ≠ 0 := mul_ne_zero ha hb
  have h12 : b*s ≠ a*s := by
    intro h
    exact hab (mul_right_cancel₀ hs h).symm
  have h13 : b*s ≠ a*b := by
    intro h
    apply has
    apply mul_left_cancel₀ hb
    calc
      b*a = a*b := mul_comm _ _
      _ = b*s := h.symm
  have h23 : a*s ≠ a*b := by
    intro h
    exact hbs (mul_left_cancel₀ ha h).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [finiteMNodes, eq_comm]



end D1Bound5
end
