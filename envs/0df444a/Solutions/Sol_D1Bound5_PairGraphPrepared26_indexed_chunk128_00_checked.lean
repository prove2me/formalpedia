-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared26.indexed_chunk128_00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:13:37.689644+00:00
-- url     : https://prove2.me/submissions/0fef7442-845f-47bd-a6d2-35a146a5186e

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_00_part0_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_00_part1_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_00_part2_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_00_part3_checked
import Theorems.Thm_D1Bound5_pairIndexedWitnessesPrefixBool_add

section
namespace D1Bound5.PairGraphPrepared26
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both mutation signs and original global destination indices are preserved. -/
theorem _root_.solution :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 128
      (witnesses.drop 0) (destinations.drop 0) = true := by
  have h064 : pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 64
      (witnesses.drop 64) (destinations.drop 64) = true := by
    apply (pairIndexedWitnessesPrefixBool_add smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 32 32
      (witnesses.drop 64) (destinations.drop 64)).trans
    refine Bool.and_eq_true_iff.mpr ⟨indexed_chunk128_00_part2_checked, ?_⟩
    simpa only [List.drop_drop, Nat.reduceAdd] using indexed_chunk128_00_part3_checked
  have h096 : pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 96
      (witnesses.drop 32) (destinations.drop 32) = true := by
    apply (pairIndexedWitnessesPrefixBool_add smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 32 64
      (witnesses.drop 32) (destinations.drop 32)).trans
    refine Bool.and_eq_true_iff.mpr ⟨indexed_chunk128_00_part1_checked, ?_⟩
    simpa only [List.drop_drop, Nat.reduceAdd] using h064
  apply (pairIndexedWitnessesPrefixBool_add smallPairA_26 smallPairB_26 anchorRoot
    (10^1100) smallPairClosure_26 32 96
    (witnesses.drop 0) (destinations.drop 0)).trans
  refine Bool.and_eq_true_iff.mpr ⟨indexed_chunk128_00_part0_checked, ?_⟩
  simpa only [List.drop_drop, Nat.reduceAdd] using h096

end D1Bound5.PairGraphPrepared26
end
