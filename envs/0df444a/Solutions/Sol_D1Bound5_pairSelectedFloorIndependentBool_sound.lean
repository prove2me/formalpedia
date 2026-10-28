-- Prove2me | solution 1 for D1Bound5.pairSelectedFloorIndependentBool_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:34.944981+00:00
-- url     : https://prove2.me/submissions/e5ef1f63-a8ea-4dba-b30c-8bb52e56fb9f

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
import Theorems.Thm_D1Bound5_pairSelectedFloorRowBool_sound

section
namespace D1Bound5
open QuadInt







theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ))
    (hcheck : pairSelectedFloorIndependentBool sieve cached rows = true) :
    pairCachedIndependentBool sieve cached = true := by
  induction cached generalizing rows with
  | nil => rfl
  | cons x xs ih =>
      cases rows with
      | nil => simp only [pairSelectedFloorIndependentBool, Bool.false_eq_true] at hcheck
      | cons item rows =>
          rcases item with ⟨code, ks⟩
          have hparts := Bool.and_eq_true_iff.mp hcheck
          apply Bool.and_eq_true_iff.mpr
          exact ⟨pairSelectedFloorRowBool_sound hd sieve x xs code ks hparts.1,
            ih rows hparts.2⟩







end D1Bound5
end
