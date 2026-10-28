-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared3.indexed_chunk07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:00.279694+00:00
-- url     : https://prove2.me/submissions/073dfcad-df37-4c82-bcce-a534264a6d0f

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
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData3_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_chunk07_part00_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_chunk07_part01_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_chunk07_part02_checked
import Theorems.Thm_D1Bound5_PairGraphPrepared3_indexed_chunk07_part03_checked
import Theorems.Thm_D1Bound5_pairIndexedWitnessesPrefixBool_add

section
namespace D1Bound5.PairGraphPrepared3
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both mutation signs use the complete original destination vertex list. -/
theorem _root_.solution :
    pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot
      (10^1100) smallPairClosure_3 64
      (witnesses.drop 448) (destinations.drop 448) = true := by
  have h32 : pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot (10^1100) smallPairClosure_3 32 (witnesses.drop 480) (destinations.drop 480) = true := by
    change pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot (10^1100) smallPairClosure_3 (16 + 16) (witnesses.drop 480) (destinations.drop 480) = true
    rw [pairIndexedWitnessesPrefixBool_add]
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact indexed_chunk07_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using indexed_chunk07_part03_checked
  have h48 : pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot (10^1100) smallPairClosure_3 48 (witnesses.drop 464) (destinations.drop 464) = true := by
    change pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot (10^1100) smallPairClosure_3 (16 + 32) (witnesses.drop 464) (destinations.drop 464) = true
    rw [pairIndexedWitnessesPrefixBool_add]
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact indexed_chunk07_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h32
  have h64 : pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot (10^1100) smallPairClosure_3 64 (witnesses.drop 448) (destinations.drop 448) = true := by
    change pairIndexedWitnessesPrefixBool smallPairA_3 smallPairB_3 anchorRoot (10^1100) smallPairClosure_3 (16 + 48) (witnesses.drop 448) (destinations.drop 448) = true
    rw [pairIndexedWitnessesPrefixBool_add]
    apply Bool.and_eq_true_iff.mpr
    constructor
    · exact indexed_chunk07_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h48
  exact h64

end D1Bound5.PairGraphPrepared3
end
