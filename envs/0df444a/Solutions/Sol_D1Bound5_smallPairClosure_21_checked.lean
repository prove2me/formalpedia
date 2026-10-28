-- Prove2me | solution 1 for D1Bound5.smallPairClosure_21_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:27:59.062816+00:00
-- url     : https://prove2.me/submissions/e88654ad-68e9-4c16-bdca-3762da2b89a5

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData21_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared21_indexed_coverage_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared21_original_witnesses_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0










theorem original_indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_21 smallPairB_21 PairGraphPrepared21.anchorRoot
      (10^1100) smallPairClosure_21 PairGraphPrepared21.witnesses PairGraphPrepared21.destinations = true :=
  pairClosureIndexedWitnessBool_of_checked_parts smallPairA_21 smallPairB_21
    PairGraphPrepared21.anchorRoot (10^1100) smallPairClosure_21
    PairGraphPrepared21.witnesses PairGraphPrepared21.destinations
    PairGraphPrepared21.indexed_coverage_checked original_witnesses_checked

end D1Bound5.PairLightClosurePrepared21
end

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared21

theorem PairGraphPrepared21.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_21 smallPairB_21 anchorRoot
      (10^1100) smallPairClosure_21 witnesses destinations = true := by
  exact PairLightClosurePrepared21.original_indexed_checked

theorem _root_.solution :
    pairClosureBool smallPairA_21 smallPairB_21
      (10^1100) smallPairClosure_21 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_21 smallPairB_21 anchorRoot
    (10^1100) smallPairClosure_21 witnesses destinations PairGraphPrepared21.indexed_checked

end D1Bound5
end
