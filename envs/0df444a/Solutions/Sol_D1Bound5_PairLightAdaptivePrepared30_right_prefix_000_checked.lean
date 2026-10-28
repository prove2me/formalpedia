-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:24.361796+00:00
-- url     : https://prove2.me/submissions/6df8976f-f56a-4c46-9252-73fa21d114a4

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_parallel_000_part07_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 92
      rightCached000 rightRows000 = true := by
  have h0084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 8
      (PairLightPrepared30.rightCached.drop 84) (PairLightPrepared30.rightRows.drop 84) = true := right_parallel_000_part07_checked
  have h0072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 20
      (PairLightPrepared30.rightCached.drop 72) (PairLightPrepared30.rightRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 8
      (PairLightPrepared30.rightCached.drop 72) (PairLightPrepared30.rightRows.drop 72)
    · exact right_parallel_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0084
  have h0060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 32
      (PairLightPrepared30.rightCached.drop 60) (PairLightPrepared30.rightRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 20
      (PairLightPrepared30.rightCached.drop 60) (PairLightPrepared30.rightRows.drop 60)
    · exact right_parallel_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0072
  have h0048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 44
      (PairLightPrepared30.rightCached.drop 48) (PairLightPrepared30.rightRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 32
      (PairLightPrepared30.rightCached.drop 48) (PairLightPrepared30.rightRows.drop 48)
    · exact right_parallel_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0060
  have h0036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 56
      (PairLightPrepared30.rightCached.drop 36) (PairLightPrepared30.rightRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 44
      (PairLightPrepared30.rightCached.drop 36) (PairLightPrepared30.rightRows.drop 36)
    · exact right_parallel_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0048
  have h0024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 68
      (PairLightPrepared30.rightCached.drop 24) (PairLightPrepared30.rightRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 56
      (PairLightPrepared30.rightCached.drop 24) (PairLightPrepared30.rightRows.drop 24)
    · exact right_parallel_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0036
  have h0012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 80
      (PairLightPrepared30.rightCached.drop 12) (PairLightPrepared30.rightRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 68
      (PairLightPrepared30.rightCached.drop 12) (PairLightPrepared30.rightRows.drop 12)
    · exact right_parallel_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0024
  have h0000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 92
      (PairLightPrepared30.rightCached.drop 0) (PairLightPrepared30.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared30.sieve 12 80
      (PairLightPrepared30.rightCached.drop 0) (PairLightPrepared30.rightRows.drop 0)
    · exact right_parallel_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0012
  exact h0000

end D1Bound5.PairLightAdaptivePrepared30
end
