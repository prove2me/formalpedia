-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared5.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:54:02.989649+00:00
-- url     : https://prove2.me/submissions/a7a16882-5ee3-470a-bcf4-2ead95b82d26

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
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData5_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk00_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk02_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk03_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk04_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk05_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk06_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk07_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk08_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk09_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk10_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk11_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk12_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_chunk13_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared5_indexed_coverage_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts
import Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_of_prefix_drop

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared5

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 witnesses destinations = true := by
  apply pairClosureIndexedWitnessBool_of_checked_parts
    smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5
    witnesses destinations indexed_coverage_checked
  have h863 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 863) (destinations.drop 863) = true := by
    rfl
  have h832 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 832) (destinations.drop 832) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 31
      (witnesses.drop 832) (destinations.drop 832) indexed_chunk13_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h863
  have h768 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 768) (destinations.drop 768) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 768) (destinations.drop 768) indexed_chunk12_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h832
  have h704 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 704) (destinations.drop 704) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 704) (destinations.drop 704) indexed_chunk11_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h768
  have h640 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 640) (destinations.drop 640) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 640) (destinations.drop 640) indexed_chunk10_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h704
  have h576 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 576) (destinations.drop 576) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 576) (destinations.drop 576) indexed_chunk09_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h640
  have h512 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 512) (destinations.drop 512) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 512) (destinations.drop 512) indexed_chunk08_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h576
  have h448 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 448) (destinations.drop 448) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 448) (destinations.drop 448) indexed_chunk07_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h512
  have h384 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 384) (destinations.drop 384) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 384) (destinations.drop 384) indexed_chunk06_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h448
  have h320 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 320) (destinations.drop 320) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 320) (destinations.drop 320) indexed_chunk05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h384
  have h256 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 256) (destinations.drop 256) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 256) (destinations.drop 256) indexed_chunk04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h320
  have h192 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 192) (destinations.drop 192) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 192) (destinations.drop 192) indexed_chunk03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h256
  have h128 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 128) (destinations.drop 128) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 128) (destinations.drop 128) indexed_chunk02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h192
  have h064 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 64) (destinations.drop 64) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 64) (destinations.drop 64) indexed_chunk01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h128
  have h000 : pairIndexedWitnessesCheckedBool smallPairA_5 smallPairB_5 anchorRoot
      (10^1100) smallPairClosure_5 (witnesses.drop 0) (destinations.drop 0) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_5 smallPairB_5 anchorRoot (10^1100) smallPairClosure_5 64
      (witnesses.drop 0) (destinations.drop 0) indexed_chunk00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h064
  simpa only [List.drop_zero] using h000



end D1Bound5
end
