-- Prove2me | solution 1 for D1Bound5.map_finiteQRowForm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:39.782039+00:00
-- url     : https://prove2.me/submissions/cd48cc34-2a9c-40dc-ad25-d0478dfa0bd4

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem map_finiteQLeft (f : R →+* S) (u v c : R) :
    f (finiteQLeft u v c) = finiteQLeft (f u) (f v) (f c) := by
  simp [finiteQLeft, map_ofNat]

@[simp] theorem map_finiteQRight (f : R →+* S) (u v c : R) :
    f (finiteQRight u v c) = finiteQRight (f u) (f v) (f c) := by
  simp [finiteQRight, map_ofNat]

@[simp] theorem map_finiteQConstant (f : R →+* S) (u v c : R) :
    f (finiteQConstant u v c) = finiteQConstant (f u) (f v) (f c) := by
  simp [finiteQConstant, map_ofNat]

@[simp] theorem map_finiteQDividedMatrix (f : R →+* S)
    (a b s t c : R) (i j : Fin 5) :
    f (finiteQDividedMatrix a b s t c i j) =
      finiteQDividedMatrix (f a) (f b) (f s) (f t) (f c) i j := by
  fin_cases i <;> fin_cases j <;> simp [finiteQDividedMatrix]



@[simp] theorem _root_.solution (f : R →+* S)
    (a b s t c z rA rB rS rT : R) (i : Fin 5) :
    f (finiteQRowForm a b s t c z rA rB rS rT i) =
      finiteQRowForm (f a) (f b) (f s) (f t) (f c)
        (f z) (f rA) (f rB) (f rS) (f rT) i := by
  simp only [finiteQRowForm, Matrix.mulVec, dotProduct, map_sum, map_mul,
    map_finiteQDividedMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  fin_cases j <;> rfl





end D1Bound5
end
