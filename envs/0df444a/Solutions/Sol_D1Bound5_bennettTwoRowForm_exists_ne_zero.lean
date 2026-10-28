-- Prove2me | solution 1 for D1Bound5.bennettTwoRowForm_exists_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:47.527126+00:00
-- url     : https://prove2.me/submissions/1bccc296-2c65-468a-8132-ce7c4e1698e6

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralMatrix_Definitions
import Theorems.Thm_D1Bound5_bennettTwoClearedMatrix_det_ne_zero

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The constructed determinant supplies an actual nonzero row whenever
the terminal root is nonzero. No nonsingularity hypothesis is supplied. -/
theorem _root_.solution
    {F : Type*} [Field F] [CharZero F]
    (a b c z sA sB : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hz : z ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ∃ i : Fin 3, bennettTwoRowForm a b c z sA sB k i ≠ 0 := by
  classical
  let Q := bennettTwoClearedMatrix a b c k
  let v : Fin 3 → F := ![z, sA/a, sB/b]
  have hdet : Q.det ≠ 0 := bennettTwoClearedMatrix_det_ne_zero a b c ha hb hab k hk
  have hunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2
    (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective Q.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hunit
  by_contra h
  push_neg at h
  have hzero : Q.mulVec v = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Q,
      bennettTwoClearedMatrix, bennettTwoRowForm] using h i
  have hv : v = 0 := hinj (by simpa using hzero)
  have hz' := congrFun hv (0 : Fin 3)
  exact hz (by simpa [v] using hz')





end D1Bound5
end
