-- Prove2me | solution 1 for D1Bound5.fiveSignedEntryGood_last_column
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:10.266784+00:00
-- url     : https://prove2.me/submissions/cda7271f-5c75-4730-9291-69bb4331021d

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
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveCompatibleSigns_Definitions
import Definitions.Def_D1Bound5_ProductFiveMatrixBridge_Definitions

section
namespace D1Bound5













/-- Last-column bounds refer to the SAME normalized five-entry matrix. -/
theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hgood : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) :
    ∀ i : Fin 4,
      ‖fiveLastError (normalizedRootError (fun k => f (a k)) u
        (fun k l => f (S k l))) i‖ < (50/99 : ℝ) ∧
      ‖fiveLastError (normalizedRootError (fun k => f (a k)) u
        (fun k l => f (S k l))) i - (1/2 : ℂ)‖ < (1/400 : ℝ) := by
  intro i
  have hi : Fin.castAdd 1 i ≠ (4 : Fin 5) := by
    intro h
    have hv := congrArg (fun k : Fin 5 => k.val) h
    change i.val = 4 at hv
    omega
  have h : SignedEntryBounds f (a (Fin.castAdd 1 i)) (a 4)
      (u (Fin.castAdd 1 i)) (u 4) (S (Fin.castAdd 1 i) 4)
      (50/99) (625/264627) := by
    simpa [FiveSignedEntryGood] using hgood (Fin.castAdd 1 i) 4 hi
  exact ⟨h.1, lt_trans h.2 (by norm_num)⟩



open scoped NumberField
open Module








end D1Bound5
end
