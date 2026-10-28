-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:28.954837+00:00
-- url     : https://prove2.me/submissions/641c3408-3c60-4e2e-b0f1-bbd4fbfc1c61

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_004_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 101
      rightCached004 rightRows004 = true := by
  have h0356 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 19
      (PairLightPrepared8.rightCached.drop 356) (PairLightPrepared8.rightRows.drop 356) = true := right_prefix_004_part05_checked
  have h0338 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 37
      (PairLightPrepared8.rightCached.drop 338) (PairLightPrepared8.rightRows.drop 338) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 18 19
      (PairLightPrepared8.rightCached.drop 338) (PairLightPrepared8.rightRows.drop 338)
    · exact right_prefix_004_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0356
  have h0321 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 54
      (PairLightPrepared8.rightCached.drop 321) (PairLightPrepared8.rightRows.drop 321) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 17 37
      (PairLightPrepared8.rightCached.drop 321) (PairLightPrepared8.rightRows.drop 321)
    · exact right_prefix_004_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0338
  have h0305 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 70
      (PairLightPrepared8.rightCached.drop 305) (PairLightPrepared8.rightRows.drop 305) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 16 54
      (PairLightPrepared8.rightCached.drop 305) (PairLightPrepared8.rightRows.drop 305)
    · exact right_prefix_004_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0321
  have h0289 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 86
      (PairLightPrepared8.rightCached.drop 289) (PairLightPrepared8.rightRows.drop 289) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 16 70
      (PairLightPrepared8.rightCached.drop 289) (PairLightPrepared8.rightRows.drop 289)
    · exact right_prefix_004_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0305
  have h0274 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 101
      (PairLightPrepared8.rightCached.drop 274) (PairLightPrepared8.rightRows.drop 274) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 15 86
      (PairLightPrepared8.rightCached.drop 274) (PairLightPrepared8.rightRows.drop 274)
    · exact right_prefix_004_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0289
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, rightCached003, rightRows003, rightCached004, rightRows004, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0274

end D1Bound5.PairLightAdaptivePrepared8
end
