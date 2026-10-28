-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared14.indexed_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:48.916113+00:00
-- url     : https://prove2.me/submissions/cef56df6-715d-4c7f-8262-1175e5c883e7

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_003

section
namespace D1Bound5.PairGraphPrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (anchorRoot * anchorRoot = smallPairA_14 * smallPairB_14 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_14) = true := by
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
    change List.zipWith (fun (z : QuadInt 0 2) (_ : QuadInt 0 2 × QuadInt 0 2) => z)
      smallPairClosure_14 rootPairs = smallPairClosure_14
    exact hzip smallPairClosure_14 rootPairs (by decide +kernel)

end D1Bound5.PairGraphPrepared14
end
