-- Prove2me | solution 1 for D1Bound5.smallPairClosure_15_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:44.294395+00:00
-- url     : https://prove2.me/submissions/5916eef9-b750-44a5-bac4-a9f0cd4cca61

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData15_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared15_indexed_coverage_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared15_original_witnesses_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0










theorem original_indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_15 smallPairB_15 PairGraphPrepared15.anchorRoot
      (10^1100) smallPairClosure_15 PairGraphPrepared15.witnesses PairGraphPrepared15.destinations = true :=
  pairClosureIndexedWitnessBool_of_checked_parts smallPairA_15 smallPairB_15
    PairGraphPrepared15.anchorRoot (10^1100) smallPairClosure_15
    PairGraphPrepared15.witnesses PairGraphPrepared15.destinations
    PairGraphPrepared15.indexed_coverage_checked original_witnesses_checked

end D1Bound5.PairLightClosurePrepared15
end

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared15

theorem PairGraphPrepared15.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_15 smallPairB_15 anchorRoot
      (10^1100) smallPairClosure_15 witnesses destinations = true := by
  exact PairLightClosurePrepared15.original_indexed_checked

theorem _root_.solution :
    pairClosureBool smallPairA_15 smallPairB_15
      (10^1100) smallPairClosure_15 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_15 smallPairB_15 anchorRoot
    (10^1100) smallPairClosure_15 witnesses destinations PairGraphPrepared15.indexed_checked

end D1Bound5
end
