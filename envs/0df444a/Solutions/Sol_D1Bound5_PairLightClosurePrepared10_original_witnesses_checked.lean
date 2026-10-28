-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared10.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:42.679652+00:00
-- url     : https://prove2.me/submissions/09b579de-afa4-442d-9298-80bfadd9ec08

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData10_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared10_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_10 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_10 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared10.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_10.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared10.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared10.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_10 smallPairB_10 PairGraphPrepared10.anchorRoot
      (10^1100) smallPairClosure_10 PairGraphPrepared10.witnesses PairGraphPrepared10.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 0 1
      (pairLightCoordinates smallPairA_10) (pairLightCoordinates smallPairB_10)
      (pairLightCoordinates PairGraphPrepared10.anchorRoot) (10^1100)
      (smallPairClosure_10.map pairLightCoordinates)
      (PairGraphPrepared10.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared10.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_10 smallPairB_10
    PairGraphPrepared10.anchorRoot (10^1100) smallPairClosure_10
    PairGraphPrepared10.witnesses PairGraphPrepared10.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared10
end
