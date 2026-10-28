-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:31:57.582426+00:00
-- url     : https://prove2.me/submissions/5681d34b-df3a-4b52-8aef-4d1c09050c40

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part07_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 88
      rightCached000 rightRows000 = true := by
  have h0084 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 4
      (PairLightPrepared14.rightCached.drop 84) (PairLightPrepared14.rightRows.drop 84) = true := right_parallel_000_part07_checked
  have h0072 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 16
      (PairLightPrepared14.rightCached.drop 72) (PairLightPrepared14.rightRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 4
      (PairLightPrepared14.rightCached.drop 72) (PairLightPrepared14.rightRows.drop 72)
    · exact right_parallel_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0084
  have h0060 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 28
      (PairLightPrepared14.rightCached.drop 60) (PairLightPrepared14.rightRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 16
      (PairLightPrepared14.rightCached.drop 60) (PairLightPrepared14.rightRows.drop 60)
    · exact right_parallel_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0072
  have h0048 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 40
      (PairLightPrepared14.rightCached.drop 48) (PairLightPrepared14.rightRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 28
      (PairLightPrepared14.rightCached.drop 48) (PairLightPrepared14.rightRows.drop 48)
    · exact right_parallel_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0060
  have h0036 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 52
      (PairLightPrepared14.rightCached.drop 36) (PairLightPrepared14.rightRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 40
      (PairLightPrepared14.rightCached.drop 36) (PairLightPrepared14.rightRows.drop 36)
    · exact right_parallel_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0048
  have h0024 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 64
      (PairLightPrepared14.rightCached.drop 24) (PairLightPrepared14.rightRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 52
      (PairLightPrepared14.rightCached.drop 24) (PairLightPrepared14.rightRows.drop 24)
    · exact right_parallel_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0036
  have h0012 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 76
      (PairLightPrepared14.rightCached.drop 12) (PairLightPrepared14.rightRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 64
      (PairLightPrepared14.rightCached.drop 12) (PairLightPrepared14.rightRows.drop 12)
    · exact right_parallel_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0024
  have h0000 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 88
      (PairLightPrepared14.rightCached.drop 0) (PairLightPrepared14.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 76
      (PairLightPrepared14.rightCached.drop 0) (PairLightPrepared14.rightRows.drop 0)
    · exact right_parallel_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0012
  exact h0000

end D1Bound5.PairLightAdaptivePrepared14
end
