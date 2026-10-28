-- Prove2me | solution 1 for D1Bound5.fiveSignedEntryGood_swap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:48:32.11749+00:00
-- url     : https://prove2.me/submissions/ca505129-60b2-4e18-83af-b0efa2f07901

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Theorems.Thm_D1Bound5_signedEntryBounds_swap

section
namespace D1Bound5





theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (i j : Fin 5) (r : R) (h : FiveSignedEntryGood f a u i j r) :
    FiveSignedEntryGood f a u j i r := by
  by_cases h4 : i = 4 ∨ j = 4
  · have h4' : j = 4 ∨ i = 4 := by tauto
    have hh : SignedEntryBounds f (a i) (a j) (u i) (u j) r
        (50/99) (625/264627) := by simpa [FiveSignedEntryGood, h4] using h
    simpa [FiveSignedEntryGood, h4'] using
      signedEntryBounds_swap f (a i) (a j) r (u i) (u j) _ _ hh
  · have h4' : ¬(j = 4 ∨ i = 4) := by tauto
    by_cases h0 : i = 0 ∨ j = 0
    · have h0' : j = 0 ∨ i = 0 := by tauto
      have hh : SignedEntryBounds f (a i) (a j) (u i) (u j) r
          (5/9) (25/486) := by simpa [FiveSignedEntryGood, h4, h0] using h
      simpa [FiveSignedEntryGood, h4', h0'] using
        signedEntryBounds_swap f (a i) (a j) r (u i) (u j) _ _ hh
    · have h0' : ¬(j = 0 ∨ i = 0) := by tauto
      have hh : SignedEntryBounds f (a i) (a j) (u i) (u j) r
          (7/13) (1/64) := by simpa [FiveSignedEntryGood, h4, h0] using h
      simpa [FiveSignedEntryGood, h4', h0'] using
        signedEntryBounds_swap f (a i) (a j) r (u i) (u j) _ _ hh











open scoped NumberField
open Module








end D1Bound5
end
