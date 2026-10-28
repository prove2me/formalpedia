-- Prove2me | solution 1 for D1Bound5.smallPairClosure_30_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:11:20.13434+00:00
-- url     : https://prove2.me/submissions/142c9bf3-ebe1-4a61-9154-786649a94077

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData30_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData30_Definitions_003
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared30_indexed_coverage_checked
import Theorems.Thm_D1Bound5_PairLightClosurePrepared30_original_witnesses_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0










theorem original_indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_30 smallPairB_30 PairGraphPrepared30.anchorRoot
      (10^1100) smallPairClosure_30 PairGraphPrepared30.witnesses PairGraphPrepared30.destinations = true :=
  pairClosureIndexedWitnessBool_of_checked_parts smallPairA_30 smallPairB_30
    PairGraphPrepared30.anchorRoot (10^1100) smallPairClosure_30
    PairGraphPrepared30.witnesses PairGraphPrepared30.destinations
    PairGraphPrepared30.indexed_coverage_checked original_witnesses_checked

end D1Bound5.PairLightClosurePrepared30
end

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared30

theorem PairGraphPrepared30.indexed_checked :
    pairClosureIndexedWitnessBool smallPairA_30 smallPairB_30 anchorRoot
      (10^1100) smallPairClosure_30 witnesses destinations = true := by
  exact PairLightClosurePrepared30.original_indexed_checked

theorem _root_.solution :
    pairClosureBool smallPairA_30 smallPairB_30
      (10^1100) smallPairClosure_30 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_30 smallPairB_30 anchorRoot
    (10^1100) smallPairClosure_30 witnesses destinations PairGraphPrepared30.indexed_checked

end D1Bound5
end
