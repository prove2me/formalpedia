-- Prove2me | solution 1 for D1Bound5.five_compatible_prefix_operator_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:49:45.363977+00:00
-- url     : https://prove2.me/submissions/7ea4ac36-2ae6-4029-93c3-aab8f5672572

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions
import Theorems.Thm_D1Bound5_fiveSignedEntryGood_prefix
import Theorems.Thm_D1Bound5_mixedFour_operator_norm_le
import Theorems.Thm_D1Bound5_normalizedRootError_diag

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

/-- The prefix from a single five-entry signed original-ring root matrix
satisfies the mixed operator-norm bound. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (S : Matrix (Fin 5) (Fin 5) R)
    (hu : ∀ i, (u i)^2 = f (a i))
    (hdiag : ∀ i, S i i = a i)
    (hgood : ∀ i j, i ≠ j → FiveSignedEntryGood f a u i j (S i j)) :
    ‖fivePrefixError (normalizedRootError (fun i => f (a i)) u
        (fun i j => f (S i j))) - halfOffDiagonal‖ ≤
      (11/96 : ℝ) := by
  let E := normalizedRootError (fun i => f (a i)) u (fun i j => f (S i j))
  let F := fivePrefixError E
  have hd : ∀ i, F i i = 0 := by
    intro i
    exact normalizedRootError_diag (fun k => f (a k)) u
      (fun k l => f (S k l)) hu
      (fun k => congrArg f (hdiag k)) (Fin.castAdd 1 i)
  have hg := fiveSignedEntryGood_prefix f a u S hgood
  have hf : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖F i j - (1/2 : ℂ)‖ < (1/18 : ℝ) := by
    intro i j hij hz
    have h : SignedEntryBounds f (a (Fin.castAdd 1 i))
        (a (Fin.castAdd 1 j)) (u (Fin.castAdd 1 i)) (u (Fin.castAdd 1 j))
        (S (Fin.castAdd 1 i) (Fin.castAdd 1 j)) (5/9) (25/486) := by
      simpa [MixedSignedEntryGood, hz] using hg i j hij
    change ‖(u (Fin.castAdd 1 i) * f (S (Fin.castAdd 1 i) (Fin.castAdd 1 j)) *
      u (Fin.castAdd 1 j) - f (a (Fin.castAdd 1 i)) *
      f (a (Fin.castAdd 1 j))) - (1/2 : ℂ)‖ < (1/18 : ℝ)
    exact lt_trans h.2 (by norm_num)
  have hl : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖F i j - (1/2 : ℂ)‖ < (1/64 : ℝ) := by
    intro i j hij hz
    have h : SignedEntryBounds f (a (Fin.castAdd 1 i))
        (a (Fin.castAdd 1 j)) (u (Fin.castAdd 1 i)) (u (Fin.castAdd 1 j))
        (S (Fin.castAdd 1 i) (Fin.castAdd 1 j)) (7/13) (1/64) := by
      simpa [MixedSignedEntryGood, hz] using hg i j hij
    change ‖(u (Fin.castAdd 1 i) * f (S (Fin.castAdd 1 i) (Fin.castAdd 1 j)) *
      u (Fin.castAdd 1 j) - f (a (Fin.castAdd 1 i)) *
      f (a (Fin.castAdd 1 j))) - (1/2 : ℂ)‖ < (1/64 : ℝ)
    exact h.2
  have hd' : ∀ i, (F - halfOffDiagonal) i i = 0 := by
    intro i
    simpa [Matrix.sub_apply, halfOffDiagonal, hd i]
  have hf' : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖(F - halfOffDiagonal) i j‖ < (1/18 : ℝ) := by
    intro i j hij hz
    simpa [Matrix.sub_apply, halfOffDiagonal, hij] using hf i j hij hz
  have hl' : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖(F - halfOffDiagonal) i j‖ < (1/64 : ℝ) := by
    intro i j hij hz
    simpa [Matrix.sub_apply, halfOffDiagonal, hij] using hl i j hij hz
  exact mixedFour_operator_norm_le (F - halfOffDiagonal) hd' hf' hl'



end D1Bound5

open scoped InnerProductSpace

namespace D1Bound5







end D1Bound5
end
