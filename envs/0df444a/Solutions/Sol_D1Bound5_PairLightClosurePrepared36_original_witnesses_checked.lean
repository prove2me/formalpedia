-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared36.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:53:51.224593+00:00
-- url     : https://prove2.me/submissions/88a6f9d8-60b1-4161-b949-d8f1a2d6c502

import Init
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
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosureBridge_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData36_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared36_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_36 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_36 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared36.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_36.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared36.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared36.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_36 smallPairB_36 PairGraphPrepared36.anchorRoot
      (10^1100) smallPairClosure_36 PairGraphPrepared36.witnesses PairGraphPrepared36.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 1 2
      (pairLightCoordinates smallPairA_36) (pairLightCoordinates smallPairB_36)
      (pairLightCoordinates PairGraphPrepared36.anchorRoot) (10^1100)
      (smallPairClosure_36.map pairLightCoordinates)
      (PairGraphPrepared36.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared36.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_36 smallPairB_36
    PairGraphPrepared36.anchorRoot (10^1100) smallPairClosure_36
    PairGraphPrepared36.witnesses PairGraphPrepared36.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared36
end
