-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared15.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:49:07.982659+00:00
-- url     : https://prove2.me/submissions/8636b69f-a54e-4d1f-aff0-895db5440626

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData15_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared15_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_15 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_15 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared15.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_15.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared15.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared15.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_15 smallPairB_15 PairGraphPrepared15.anchorRoot
      (10^1100) smallPairClosure_15 PairGraphPrepared15.witnesses PairGraphPrepared15.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 0 2
      (pairLightCoordinates smallPairA_15) (pairLightCoordinates smallPairB_15)
      (pairLightCoordinates PairGraphPrepared15.anchorRoot) (10^1100)
      (smallPairClosure_15.map pairLightCoordinates)
      (PairGraphPrepared15.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared15.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_15 smallPairB_15
    PairGraphPrepared15.anchorRoot (10^1100) smallPairClosure_15
    PairGraphPrepared15.witnesses PairGraphPrepared15.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared15
end
