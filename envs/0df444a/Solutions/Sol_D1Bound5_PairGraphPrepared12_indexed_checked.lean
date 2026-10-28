-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared12.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:53:44.453981+00:00
-- url     : https://prove2.me/submissions/bbc90051-0a39-460c-b2a1-9c0c6eaf8533

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
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData12_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk00_part00_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk00_part01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk02_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk03_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk04_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_chunk05_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared12_indexed_coverage_checked
import Theorems.Thm_D1Bound5_pairClosureIndexedWitnessBool_of_checked_parts
import Theorems.Thm_D1Bound5_pairIndexedWitnessesCheckedBool_of_prefix_drop
import Theorems.Thm_D1Bound5_pairIndexedWitnessesPrefixBool_add

section
namespace D1Bound5.PairGraphPrepared12
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Full original vertex list and both signs; only aligned row lists are sliced. -/
theorem indexed_chunk00_checked :
    pairIndexedWitnessesPrefixBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 128
      (witnesses.drop 0) (destinations.drop 0) = true := by
  exact (pairIndexedWitnessesPrefixBool_add smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 64 64 (witnesses.drop 0) (destinations.drop 0)).trans
    (Bool.and_eq_true_iff.mpr ⟨indexed_chunk00_part00_checked, by
      simpa only [List.drop_drop, Nat.reduceAdd] using indexed_chunk00_part01_checked⟩)

end D1Bound5.PairGraphPrepared12
end

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared12

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 witnesses destinations = true := by
  apply pairClosureIndexedWitnessBool_of_checked_parts
    smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12
    witnesses destinations indexed_coverage_checked
  have h006 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 720) (destinations.drop 720) = true := by
    rfl
  have h005 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 640)
      (destinations.drop 640) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12 80
      (witnesses.drop 640) (destinations.drop 640)
      indexed_chunk05_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h006
  have h004 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 512)
      (destinations.drop 512) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12 128
      (witnesses.drop 512) (destinations.drop 512)
      indexed_chunk04_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h005
  have h003 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 384)
      (destinations.drop 384) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12 128
      (witnesses.drop 384) (destinations.drop 384)
      indexed_chunk03_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h004
  have h002 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 256)
      (destinations.drop 256) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12 128
      (witnesses.drop 256) (destinations.drop 256)
      indexed_chunk02_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h003
  have h001 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 128)
      (destinations.drop 128) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12 128
      (witnesses.drop 128) (destinations.drop 128)
      indexed_chunk01_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h002
  have h000 : pairIndexedWitnessesCheckedBool smallPairA_12 smallPairB_12 anchorRoot
      (10^1100) smallPairClosure_12 (witnesses.drop 0)
      (destinations.drop 0) = true := by
    apply pairIndexedWitnessesCheckedBool_of_prefix_drop
      smallPairA_12 smallPairB_12 anchorRoot (10^1100) smallPairClosure_12 128
      (witnesses.drop 0) (destinations.drop 0)
      indexed_chunk00_checked
    simpa only [List.drop_drop, Nat.reduceAdd] using h001
  simpa only [List.drop_zero] using h000



end D1Bound5
end
