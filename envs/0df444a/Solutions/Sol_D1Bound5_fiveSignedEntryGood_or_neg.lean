-- Prove2me | solution 1 for D1Bound5.fiveSignedEntryGood_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:32.49102+00:00
-- url     : https://prove2.me/submissions/5726c169-ed41-4c5e-8ed5-29e8ecef86f5

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
import Theorems.Thm_D1Bound5_signedEntryBounds_fiftyfour_or_neg
import Theorems.Thm_D1Bound5_signedEntryBounds_nine_or_neg
import Theorems.Thm_D1Bound5_signedEntryBounds_three_or_neg

section
namespace D1Bound5







theorem _root_.solution {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 5 → R) (u : Fin 5 → ℂ)
    (i j : Fin 5) (r : R)
    (hu : ∀ k, (u k)^2 = f (a k))
    (hr : r^2 = a i*a j+1)
    (hfirst : 3 ≤ ‖f (a i)*f (a j)‖)
    (hlater : ¬(i = 0 ∨ j = 0) → 9 ≤ ‖f (a i)*f (a j)‖)
    (hlast : i = 4 ∨ j = 4 → 54 ≤ ‖f (a i)*f (a j)‖) :
    FiveSignedEntryGood f a u i j r ∨ FiveSignedEntryGood f a u i j (-r) := by
  unfold FiveSignedEntryGood
  split_ifs with h4 h0
  · exact signedEntryBounds_fiftyfour_or_neg f (a i) (a j) r
      (u i) (u j) (hu i) (hu j) hr (hlast h4)
  · exact signedEntryBounds_three_or_neg f (a i) (a j) r
      (u i) (u j) (hu i) (hu j) hr hfirst
  · exact signedEntryBounds_nine_or_neg f (a i) (a j) r
      (u i) (u j) (hu i) (hu j) hr (hlater h0)









open scoped NumberField
open Module








end D1Bound5
end
