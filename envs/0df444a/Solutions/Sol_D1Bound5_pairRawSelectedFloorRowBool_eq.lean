-- Prove2me | solution 1 for D1Bound5.pairRawSelectedFloorRowBool_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:52.862712+00:00
-- url     : https://prove2.me/submissions/6354a3b6-68a6-410d-9ac7-eb6e97466196

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
import Definitions.Def_D1Bound5_PairNegativeIntegerObstruction_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_QuadSquareFloorObstruction_Definitions
import Theorems.Thm_D1Bound5_pairSelectedCachedMaskNatRejectBool_eq

section
namespace D1Bound5







/-- Equality holds for arbitrary words, signatures, and floor lists,
including malformed certificates; this is not merely one-way soundness. -/
theorem _root_.solution {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (x : PairResidueVertex tau nu) (ys : List (PairResidueVertex tau nu))
    (code : ℕ) (ks : List ℕ) :
    pairRawSelectedFloorRowBool sieve x ys code ks =
      pairSelectedFloorRowBool sieve x ys code ks := by
  induction ys generalizing code ks with
  | nil => rfl
  | cons y ys ih =>
      cases ks <;>
        simp only [pairRawSelectedFloorRowBool, pairSelectedFloorRowBool,
          pairSelectedCachedMaskNatRejectBool_eq, ih]











end D1Bound5
end
