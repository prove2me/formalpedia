-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared7.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:51:56.60471+00:00
-- url     : https://prove2.me/submissions/13766d3e-0e4d-4c03-b615-004082512c2b

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData7_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk00_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk02_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk03_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk04_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk05_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk06_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk07_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk08_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk09_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk10_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk11_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk12_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_chunk13_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared7_indexed_coverage_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts
import Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_of_prefix_drop

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared7

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 witnesses destinations = true := by
  apply pairClosureIndexedWitnessBool_of_checked_parts
    smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7
    witnesses destinations indexed_coverage_checked
  have h864 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 864) (destinations.drop 864) = true := by
    rfl
  have h832 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 832) (destinations.drop 832) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 32
      (witnesses.drop 832) (destinations.drop 832) indexed_chunk13_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h864
  have h768 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 768) (destinations.drop 768) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 768) (destinations.drop 768) indexed_chunk12_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h832
  have h704 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 704) (destinations.drop 704) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 704) (destinations.drop 704) indexed_chunk11_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h768
  have h640 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 640) (destinations.drop 640) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 640) (destinations.drop 640) indexed_chunk10_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h704
  have h576 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 576) (destinations.drop 576) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 576) (destinations.drop 576) indexed_chunk09_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h640
  have h512 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 512) (destinations.drop 512) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 512) (destinations.drop 512) indexed_chunk08_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h576
  have h448 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 448) (destinations.drop 448) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 448) (destinations.drop 448) indexed_chunk07_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h512
  have h384 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 384) (destinations.drop 384) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 384) (destinations.drop 384) indexed_chunk06_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h448
  have h320 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 320) (destinations.drop 320) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 320) (destinations.drop 320) indexed_chunk05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h384
  have h256 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 256) (destinations.drop 256) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 256) (destinations.drop 256) indexed_chunk04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h320
  have h192 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 192) (destinations.drop 192) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 192) (destinations.drop 192) indexed_chunk03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h256
  have h128 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 128) (destinations.drop 128) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 128) (destinations.drop 128) indexed_chunk02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h192
  have h064 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 64) (destinations.drop 64) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 64) (destinations.drop 64) indexed_chunk01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h128
  have h000 : pairIndexedWitnessesCheckedBool smallPairA_7 smallPairB_7 anchorRoot
      (10^1100) smallPairClosure_7 (witnesses.drop 0) (destinations.drop 0) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_7 smallPairB_7 anchorRoot (10^1100) smallPairClosure_7 64
      (witnesses.drop 0) (destinations.drop 0) indexed_chunk00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h064
  simpa only [List.drop_zero] using h000



end D1Bound5
end
