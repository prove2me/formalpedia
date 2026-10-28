-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared23.original_witnesses_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:52:28.047128+00:00
-- url     : https://prove2.me/submissions/0d00c448-5472-49aa-9882-a0bab07c861d

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData23_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData23_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions
import Theorems.Thm_D1Bound5_PairLightClosurePrepared23_all_checked
import Theorems.Thm_D1Bound5_pairLightIndexedWitnessesCheckedBool_eq

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem a_eq : a = pairLightCoordinates smallPairA_23 := by rfl
theorem b_eq : b = pairLightCoordinates smallPairB_23 := by rfl
theorem anchorRoot_eq : anchorRoot = pairLightCoordinates PairGraphPrepared23.anchorRoot := by rfl
theorem vertices_eq : vertices = smallPairClosure_23.map pairLightCoordinates := by rfl
theorem witnesses_eq : witnesses = PairGraphPrepared23.witnesses.map pairLightRootWitnessCoordinates := by rfl
theorem destinations_eq : destinations = PairGraphPrepared23.destinations := by rfl

theorem _root_.solution :
    pairIndexedWitnessesCheckedBool smallPairA_23 smallPairB_23 PairGraphPrepared23.anchorRoot
      (10^1100) smallPairClosure_23 PairGraphPrepared23.witnesses PairGraphPrepared23.destinations = true := by
  have hcheck : pairLightIndexedWitnessesCheckedBool 1 1
      (pairLightCoordinates smallPairA_23) (pairLightCoordinates smallPairB_23)
      (pairLightCoordinates PairGraphPrepared23.anchorRoot) (10^1100)
      (smallPairClosure_23.map pairLightCoordinates)
      (PairGraphPrepared23.witnesses.map pairLightRootWitnessCoordinates) PairGraphPrepared23.destinations = true := by
    rw [← a_eq, ← b_eq, ← anchorRoot_eq, ← vertices_eq, ← witnesses_eq, ← destinations_eq]
    exact all_checked
  exact (pairLightIndexedWitnessesCheckedBool_eq smallPairA_23 smallPairB_23
    PairGraphPrepared23.anchorRoot (10^1100) smallPairClosure_23
    PairGraphPrepared23.witnesses PairGraphPrepared23.destinations).symm.trans hcheck



end D1Bound5.PairLightClosurePrepared23
end
