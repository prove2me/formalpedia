-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared26.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:53:52.88601+00:00
-- url     : https://prove2.me/submissions/2ddf581f-28d4-42d2-bc0e-8470771cab4a

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_00_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_02_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_03_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_04_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_05_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_06_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_07_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_08_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_09_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_chunk128_10_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_coverage_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_tail128_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts
import Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_of_prefix_drop

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared26

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 witnesses destinations = true := by
  apply pairClosureIndexedWitnessBool_of_checked_parts
    smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26
    witnesses destinations indexed_coverage_checked
  have h012 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 1525) (destinations.drop 1525) = true := by
    rfl
  have h011 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 1397)
      (destinations.drop 1397) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 1397) (destinations.drop 1397)
      indexed_tail128_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h012
  have h010 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 1280)
      (destinations.drop 1280) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 117
      (witnesses.drop 1280) (destinations.drop 1280)
      indexed_chunk128_10_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h011
  have h009 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 1152)
      (destinations.drop 1152) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 1152) (destinations.drop 1152)
      indexed_chunk128_09_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h010
  have h008 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 1024)
      (destinations.drop 1024) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 1024) (destinations.drop 1024)
      indexed_chunk128_08_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h009
  have h007 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 896)
      (destinations.drop 896) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 896) (destinations.drop 896)
      indexed_chunk128_07_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h008
  have h006 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 768)
      (destinations.drop 768) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 768) (destinations.drop 768)
      indexed_chunk128_06_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h007
  have h005 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 640)
      (destinations.drop 640) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 640) (destinations.drop 640)
      indexed_chunk128_05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h006
  have h004 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 512)
      (destinations.drop 512) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 512) (destinations.drop 512)
      indexed_chunk128_04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h005
  have h003 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 384)
      (destinations.drop 384) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 384) (destinations.drop 384)
      indexed_chunk128_03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h004
  have h002 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 256)
      (destinations.drop 256) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 256) (destinations.drop 256)
      indexed_chunk128_02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h003
  have h001 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 128)
      (destinations.drop 128) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 128) (destinations.drop 128)
      indexed_chunk128_01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h002
  have h000 : pairIndexedWitnessesCheckedBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 (witnesses.drop 0)
      (destinations.drop 0) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_26 smallPairB_26 anchorRoot (10^1100) smallPairClosure_26 128
      (witnesses.drop 0) (destinations.drop 0)
      indexed_chunk128_00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h001
  simpa only [List.drop_zero] using h000



end D1Bound5
end
