-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared24.indexed_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:17:17.904227+00:00
-- url     : https://prove2.me/submissions/cbcc27d7-69cb-4e45-8960-fa8ce6a38a14

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData24_Definitions_003

section
namespace D1Bound5.PairGraphPrepared24
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (anchorRoot * anchorRoot = smallPairA_24 * smallPairB_24 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_24) = true := by
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
    change List.zipWith (fun (z : QuadInt 1 1) (_ : QuadInt 1 1 × QuadInt 1 1) => z)
      smallPairClosure_24 rootPairs = smallPairClosure_24
    exact hzip smallPairClosure_24 rootPairs (by decide +kernel)

end D1Bound5.PairGraphPrepared24
end
