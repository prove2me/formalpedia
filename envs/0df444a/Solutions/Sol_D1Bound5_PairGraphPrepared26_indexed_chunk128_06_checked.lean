-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared26.indexed_chunk128_06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:04.856882+00:00
-- url     : https://prove2.me/submissions/91a7f921-9df5-48c6-bc00-c4e088b931c9

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
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_06_part0_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_06_part1_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_06_part2_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_06_part3_checked
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
      (witnesses.drop 768) (destinations.drop 768) = true := by
  have h064 : pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 64
      (witnesses.drop 832) (destinations.drop 832) = true := by
    apply (pairIndexedWitnessesPrefixBool_add smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 32 32
      (witnesses.drop 832) (destinations.drop 832)).trans
    refine Bool.and_eq_true_iff.mpr ⟨indexed_chunk128_06_part2_checked, ?_⟩
    simpa only [List.drop_drop, Nat.reduceAdd] using indexed_chunk128_06_part3_checked
  have h096 : pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 96
      (witnesses.drop 800) (destinations.drop 800) = true := by
    apply (pairIndexedWitnessesPrefixBool_add smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 32 64
      (witnesses.drop 800) (destinations.drop 800)).trans
    refine Bool.and_eq_true_iff.mpr ⟨indexed_chunk128_06_part1_checked, ?_⟩
    simpa only [List.drop_drop, Nat.reduceAdd] using h064
  apply (pairIndexedWitnessesPrefixBool_add smallPairA_26 smallPairB_26 anchorRoot
    (10^1100) smallPairClosure_26 32 96
    (witnesses.drop 768) (destinations.drop 768)).trans
  refine Bool.and_eq_true_iff.mpr ⟨indexed_chunk128_06_part0_checked, ?_⟩
  simpa only [List.drop_drop, Nat.reduceAdd] using h096

end D1Bound5.PairGraphPrepared26
end
