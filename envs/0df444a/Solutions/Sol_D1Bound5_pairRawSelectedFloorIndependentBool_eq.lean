-- Prove2me | solution 1 for D1Bound5.pairRawSelectedFloorIndependentBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:11:00.070949+00:00
-- url     : https://prove2.me/submissions/9684ac5e-10c3-4aa9-9ec0-919b29b65a87

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
import Theorems.Thm_D1Bound5_pairRawSelectedFloorRowBool_eq

section
namespace D1Bound5











theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ)) :
    pairRawSelectedFloorIndependentBool sieve cached rows =
      pairSelectedFloorIndependentBool sieve cached rows := by
  induction cached generalizing rows with
  | nil => cases rows <;> rfl
  | cons x xs ih =>
      cases rows with
      | nil => rfl
      | cons item rows =>
          rcases item with ⟨code, ks⟩
          simp only [pairRawSelectedFloorIndependentBool, pairSelectedFloorIndependentBool,
            pairRawSelectedFloorRowBool_eq, ih]







end D1Bound5
end
