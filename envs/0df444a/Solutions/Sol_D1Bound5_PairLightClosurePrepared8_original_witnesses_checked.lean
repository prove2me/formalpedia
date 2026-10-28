-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared8.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:49:01.675023+00:00
-- url     : https://prove2.me/submissions/117bd3c2-c861-49a3-b0ef-3b5a6d21277a

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs8_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs8_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData8_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData8_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared8_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_8 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_8 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared8.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_8.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared8.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared8.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_8 smallPairB_8 PairGraphPrepared8.anchorRoot
      (10^1100) smallPairClosure_8 PairGraphPrepared8.witnesses PairGraphPrepared8.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 0 1
      (pairLightCoordinates smallPairA_8) (pairLightCoordinates smallPairB_8)
      (pairLightCoordinates PairGraphPrepared8.anchorRoot) (10^1100)
      (smallPairClosure_8.map pairLightCoordinates)
      (PairGraphPrepared8.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared8.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_8 smallPairB_8
    PairGraphPrepared8.anchorRoot (10^1100) smallPairClosure_8
    PairGraphPrepared8.witnesses PairGraphPrepared8.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared8
end
