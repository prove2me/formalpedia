-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared14.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:57:28.464689+00:00
-- url     : https://prove2.me/submissions/8ae6df03-9ae3-40f2-8e66-b3e8400b01cd

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared14_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_14 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_14 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared14.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_14.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared14.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared14.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_14 smallPairB_14 PairGraphPrepared14.anchorRoot
      (10^1100) smallPairClosure_14 PairGraphPrepared14.witnesses PairGraphPrepared14.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 0 2
      (pairLightCoordinates smallPairA_14) (pairLightCoordinates smallPairB_14)
      (pairLightCoordinates PairGraphPrepared14.anchorRoot) (10^1100)
      (smallPairClosure_14.map pairLightCoordinates)
      (PairGraphPrepared14.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared14.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_14 smallPairB_14
    PairGraphPrepared14.anchorRoot (10^1100) smallPairClosure_14
    PairGraphPrepared14.witnesses PairGraphPrepared14.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared14
end
