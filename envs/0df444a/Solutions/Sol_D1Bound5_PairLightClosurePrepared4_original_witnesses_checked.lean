-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared4.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:55:40.197989+00:00
-- url     : https://prove2.me/submissions/ccbcea5b-4e54-48c1-8821-8546594f1ff1

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData4_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared4_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_4 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_4 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared4.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_4.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared4.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared4.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_4 smallPairB_4 PairGraphPrepared4.anchorRoot
      (10^1100) smallPairClosure_4 PairGraphPrepared4.witnesses PairGraphPrepared4.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 0 1
      (pairLightCoordinates smallPairA_4) (pairLightCoordinates smallPairB_4)
      (pairLightCoordinates PairGraphPrepared4.anchorRoot) (10^1100)
      (smallPairClosure_4.map pairLightCoordinates)
      (PairGraphPrepared4.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared4.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_4 smallPairB_4
    PairGraphPrepared4.anchorRoot (10^1100) smallPairClosure_4
    PairGraphPrepared4.witnesses PairGraphPrepared4.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared4
end
