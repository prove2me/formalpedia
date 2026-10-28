-- Prove2me | solution 1 for D1Bound5.fiveSignedEntryGood_prefix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:49.759165+00:00
-- url     : https://prove2.me/submissions/f47cd444-da09-4f78-ac85-b6293fae08f6

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

section
namespace D1Bound5











/-- A simultaneous five-entry choice retains the existing mixed prefix predicate. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hgood : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) :
    ∀ i j : Fin 4, i ≠ j →
      MixedSignedEntryGood f (fun k => a (Fin.castAdd 1 k))
        (fun k => u (Fin.castAdd 1 k)) i j
        (S (Fin.castAdd 1 i) (Fin.castAdd 1 j)) := by
  have h4 (i : Fin 4) : Fin.castAdd 1 i ≠ (4 : Fin 5) := by
    intro h
    have hv := congrArg (fun k : Fin 5 => k.val) h
    change i.val = 4 at hv
    omega
  have h0 (i : Fin 4) : Fin.castAdd 1 i = (0 : Fin 5) ↔ i = 0 := by
    constructor
    · intro h
      apply Fin.ext
      exact congrArg (fun k : Fin 5 => k.val) h
    · intro h
      subst i
      rfl
  intro i j hij
  have hne : Fin.castAdd 1 i ≠ Fin.castAdd 1 j := by
    intro h
    exact hij (Fin.ext (congrArg (fun k : Fin 5 => k.val) h))
  have h := hgood (Fin.castAdd 1 i) (Fin.castAdd 1 j) hne
  simpa only [FiveSignedEntryGood, h4 i, h4 j, false_or, ite_false,
    h0 i, h0 j, MixedSignedEntryGood] using h





open scoped NumberField
open Module








end D1Bound5
end
