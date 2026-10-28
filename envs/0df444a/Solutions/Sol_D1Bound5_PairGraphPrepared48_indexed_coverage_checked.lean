-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared48.indexed_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:20.955841+00:00
-- url     : https://prove2.me/submissions/2493fb0a-66f7-4b04-941c-dddd619ddbed

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
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData48_Definitions_003

section
namespace D1Bound5.PairGraphPrepared48
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (anchorRoot * anchorRoot = smallPairA_48 * smallPairB_48 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_48) = true := by
  have hzip {α β : Type} (xs : List α) (ys : List β)
      (hlen : xs.length ≤ ys.length) :
      List.zipWith (fun x _ => x) xs ys = xs := by
    induction xs generalizing ys with
    | nil => rfl
    | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
        exact congrArg (List.cons x) (ih ys (Nat.le_of_succ_le_succ hlen))
  apply decide_eq_true
  constructor
  · decide +kernel
  · unfold witnesses
    rw [List.map_zipWith]
    change List.zipWith (fun (z : QuadInt 1 8) (_ : QuadInt 1 8 × QuadInt 1 8) => z)
      smallPairClosure_48 rootPairs = smallPairClosure_48
    exact hzip smallPairClosure_48 rootPairs (by decide +kernel)

end D1Bound5.PairGraphPrepared48
end
