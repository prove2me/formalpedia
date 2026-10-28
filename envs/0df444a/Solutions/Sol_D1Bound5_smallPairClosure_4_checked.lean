-- Prove2me | solution 1 for D1Bound5.smallPairClosure_4_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:27:57.549626+00:00
-- url     : https://prove2.me/submissions/aefd413f-3d2c-4160-9b61-f7ad31bcda4f

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData4_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared4_indexed_coverage_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared4_original_witnesses_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0










theorem original_indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_4 smallPairB_4 PairGraphPrepared4.anchorRoot
      (10^1100) smallPairClosure_4 PairGraphPrepared4.witnesses PairGraphPrepared4.destinations = true :=
  pairClosureIndexedWitnessBool_of_checked_parts smallPairA_4 smallPairB_4
    PairGraphPrepared4.anchorRoot (10^1100) smallPairClosure_4
    PairGraphPrepared4.witnesses PairGraphPrepared4.destinations
    PairGraphPrepared4.indexed_coverage_checked original_witnesses_checked

end D1Bound5.PairLightClosurePrepared4
end

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared4

theorem PairGraphPrepared4.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_4 smallPairB_4 anchorRoot
      (10^1100) smallPairClosure_4 witnesses destinations = true := by
  exact PairLightClosurePrepared4.original_indexed_checked

theorem _root_.solution :
    pairClosureBool smallPairA_4 smallPairB_4
      (10^1100) smallPairClosure_4 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_4 smallPairB_4 anchorRoot
    (10^1100) smallPairClosure_4 witnesses destinations PairGraphPrepared4.indexed_checked

end D1Bound5
end
