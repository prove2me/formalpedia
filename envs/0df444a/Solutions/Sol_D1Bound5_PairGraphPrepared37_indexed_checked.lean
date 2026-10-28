-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared37.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:52:54.911286+00:00
-- url     : https://prove2.me/submissions/be8937b5-be5c-4564-907a-6b763fd812b0

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData37_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk00_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk02_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk03_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk04_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk05_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk06_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk07_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk08_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk09_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk10_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_chunk11_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts
import Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_of_prefix_drop

section
set_option autoImplicit false

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared37

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 witnesses destinations = true := by
  have hcoverage : decide (anchorRoot * anchorRoot = smallPairA_37 * smallPairB_37 + 1 ∧
      witnesses.map PairRootWitness.vertex = smallPairClosure_37) = true := by
    decide +kernel
  apply pairClosureIndexedWitnessBool_of_checked_parts
    smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37
    witnesses destinations hcoverage
  have h012 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 746) (destinations.drop 746) = true := by
    rfl
  have h011 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 704)
      (destinations.drop 704) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 42
      (witnesses.drop 704) (destinations.drop 704)
      indexed_chunk11_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h012
  have h010 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 640)
      (destinations.drop 640) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 640) (destinations.drop 640)
      indexed_chunk10_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h011
  have h009 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 576)
      (destinations.drop 576) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 576) (destinations.drop 576)
      indexed_chunk09_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h010
  have h008 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 512)
      (destinations.drop 512) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 512) (destinations.drop 512)
      indexed_chunk08_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h009
  have h007 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 448)
      (destinations.drop 448) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 448) (destinations.drop 448)
      indexed_chunk07_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h008
  have h006 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 384)
      (destinations.drop 384) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 384) (destinations.drop 384)
      indexed_chunk06_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h007
  have h005 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 320)
      (destinations.drop 320) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 320) (destinations.drop 320)
      indexed_chunk05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h006
  have h004 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 256)
      (destinations.drop 256) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 256) (destinations.drop 256)
      indexed_chunk04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h005
  have h003 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 192)
      (destinations.drop 192) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 192) (destinations.drop 192)
      indexed_chunk03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h004
  have h002 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 128)
      (destinations.drop 128) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 128) (destinations.drop 128)
      indexed_chunk02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h003
  have h001 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 64)
      (destinations.drop 64) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 64) (destinations.drop 64)
      indexed_chunk01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h002
  have h000 : pairIndexedWitnessesCheckedBool smallPairA_37 smallPairB_37 anchorRoot
      (10^1100) smallPairClosure_37 (witnesses.drop 0)
      (destinations.drop 0) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_37 smallPairB_37 anchorRoot (10^1100) smallPairClosure_37 64
      (witnesses.drop 0) (destinations.drop 0)
      indexed_chunk00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h001
  simpa only [List.drop_zero] using h000



end D1Bound5
end
