-- Prove2me | solution 1 for D1Bound5.finiteMRowForm_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:12.266507+00:00
-- url     : https://prove2.me/submissions/f97155ce-e52d-4ae7-8064-7c20ecc92a5a

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Theorems.Thm_D1Bound5_finiteMDividedMatrix_det_ne_zero

section
open scoped NumberField
open Module

namespace D1Bound5





theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (a b s c z rA rB rS : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (hz : z ≠ 0) :
    ∃ i : Fin 4, finiteMRowForm a b s c z rA rB rS i ≠ 0 := by
  classical
  let M := finiteMDividedMatrix a b s c
  let v : Fin 4 → F := ![z,rA,rB,rS]
  have hdet : M.det ≠ 0 := finiteMDividedMatrix_det_ne_zero a b s c ha hb hs hab has hbs
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.mpr hdet)
  have hi : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hu
  by_contra h
  push_neg at h
  have hzero : M.mulVec v = 0 := by funext i; exact h i
  have hv : v = 0 := hi (by simpa using hzero)
  exact hz (by simpa [v] using congrFun hv (0 : Fin 4))



end D1Bound5
end
