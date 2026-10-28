-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:31:54.607184+00:00
-- url     : https://prove2.me/submissions/1c99aa24-5f2d-4b34-af6e-f19611a454b9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part10_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 122
      rightCached001 rightRows001 = true := by
  have h0212 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 2
      (PairLightPrepared15.rightCached.drop 212) (PairLightPrepared15.rightRows.drop 212) = true := right_parallel_001_part10_checked
  have h0200 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 14
      (PairLightPrepared15.rightCached.drop 200) (PairLightPrepared15.rightRows.drop 200) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 2
      (PairLightPrepared15.rightCached.drop 200) (PairLightPrepared15.rightRows.drop 200)
    · exact right_parallel_001_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0212
  have h0188 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 26
      (PairLightPrepared15.rightCached.drop 188) (PairLightPrepared15.rightRows.drop 188) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 14
      (PairLightPrepared15.rightCached.drop 188) (PairLightPrepared15.rightRows.drop 188)
    · exact right_parallel_001_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0200
  have h0176 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 38
      (PairLightPrepared15.rightCached.drop 176) (PairLightPrepared15.rightRows.drop 176) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 26
      (PairLightPrepared15.rightCached.drop 176) (PairLightPrepared15.rightRows.drop 176)
    · exact right_parallel_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0188
  have h0164 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 50
      (PairLightPrepared15.rightCached.drop 164) (PairLightPrepared15.rightRows.drop 164) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 38
      (PairLightPrepared15.rightCached.drop 164) (PairLightPrepared15.rightRows.drop 164)
    · exact right_parallel_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0176
  have h0152 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 62
      (PairLightPrepared15.rightCached.drop 152) (PairLightPrepared15.rightRows.drop 152) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 50
      (PairLightPrepared15.rightCached.drop 152) (PairLightPrepared15.rightRows.drop 152)
    · exact right_parallel_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0164
  have h0140 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 74
      (PairLightPrepared15.rightCached.drop 140) (PairLightPrepared15.rightRows.drop 140) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 62
      (PairLightPrepared15.rightCached.drop 140) (PairLightPrepared15.rightRows.drop 140)
    · exact right_parallel_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0152
  have h0128 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 86
      (PairLightPrepared15.rightCached.drop 128) (PairLightPrepared15.rightRows.drop 128) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 74
      (PairLightPrepared15.rightCached.drop 128) (PairLightPrepared15.rightRows.drop 128)
    · exact right_parallel_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0140
  have h0116 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 98
      (PairLightPrepared15.rightCached.drop 116) (PairLightPrepared15.rightRows.drop 116) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 86
      (PairLightPrepared15.rightCached.drop 116) (PairLightPrepared15.rightRows.drop 116)
    · exact right_parallel_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0128
  have h0104 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 110
      (PairLightPrepared15.rightCached.drop 104) (PairLightPrepared15.rightRows.drop 104) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 98
      (PairLightPrepared15.rightCached.drop 104) (PairLightPrepared15.rightRows.drop 104)
    · exact right_parallel_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0116
  have h0092 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 122
      (PairLightPrepared15.rightCached.drop 92) (PairLightPrepared15.rightRows.drop 92) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 110
      (PairLightPrepared15.rightCached.drop 92) (PairLightPrepared15.rightRows.drop 92)
    · exact right_parallel_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0104
  exact h0092

end D1Bound5.PairLightAdaptivePrepared15
end
