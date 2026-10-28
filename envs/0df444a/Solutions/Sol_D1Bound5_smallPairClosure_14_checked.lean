-- Prove2me | solution 1 for D1Bound5.smallPairClosure_14_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:33:25.342083+00:00
-- url     : https://prove2.me/submissions/458468cc-bee7-4332-9946-c580648b95b8

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData14_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared14_indexed_coverage_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared14_original_witnesses_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0










theorem original_indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_14 smallPairB_14 PairGraphPrepared14.anchorRoot
      (10^1100) smallPairClosure_14 PairGraphPrepared14.witnesses PairGraphPrepared14.destinations = true :=
  pairClosureIndexedWitnessBool_of_checked_parts smallPairA_14 smallPairB_14
    PairGraphPrepared14.anchorRoot (10^1100) smallPairClosure_14
    PairGraphPrepared14.witnesses PairGraphPrepared14.destinations
    PairGraphPrepared14.indexed_coverage_checked original_witnesses_checked

end D1Bound5.PairLightClosurePrepared14
end

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared14

theorem PairGraphPrepared14.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_14 smallPairB_14 anchorRoot
      (10^1100) smallPairClosure_14 witnesses destinations = true := by
  exact PairLightClosurePrepared14.original_indexed_checked

theorem _root_.solution :
    pairClosureBool smallPairA_14 smallPairB_14
      (10^1100) smallPairClosure_14 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_14 smallPairB_14 anchorRoot
    (10^1100) smallPairClosure_14 witnesses destinations PairGraphPrepared14.indexed_checked

end D1Bound5
end
