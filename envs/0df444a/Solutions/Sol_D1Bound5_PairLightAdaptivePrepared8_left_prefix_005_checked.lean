-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:41.062792+00:00
-- url     : https://prove2.me/submissions/699dc622-6e9e-40c4-9d82-0a55bd06739b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_005_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 151
      leftCached005 leftRows005 = true := by
  have h0524 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 3
      (PairLightPrepared8.leftCached.drop 524) (PairLightPrepared8.leftRows.drop 524) = true := left_prefix_005_part06_checked
  have h0493 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 34
      (PairLightPrepared8.leftCached.drop 493) (PairLightPrepared8.leftRows.drop 493) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 31 3
      (PairLightPrepared8.leftCached.drop 493) (PairLightPrepared8.leftRows.drop 493)
    · exact left_prefix_005_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0524
  have h0465 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 62
      (PairLightPrepared8.leftCached.drop 465) (PairLightPrepared8.leftRows.drop 465) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 28 34
      (PairLightPrepared8.leftCached.drop 465) (PairLightPrepared8.leftRows.drop 465)
    · exact left_prefix_005_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0493
  have h0440 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 87
      (PairLightPrepared8.leftCached.drop 440) (PairLightPrepared8.leftRows.drop 440) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 25 62
      (PairLightPrepared8.leftCached.drop 440) (PairLightPrepared8.leftRows.drop 440)
    · exact left_prefix_005_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0465
  have h0417 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 110
      (PairLightPrepared8.leftCached.drop 417) (PairLightPrepared8.leftRows.drop 417) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 23 87
      (PairLightPrepared8.leftCached.drop 417) (PairLightPrepared8.leftRows.drop 417)
    · exact left_prefix_005_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0440
  have h0396 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 131
      (PairLightPrepared8.leftCached.drop 396) (PairLightPrepared8.leftRows.drop 396) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 21 110
      (PairLightPrepared8.leftCached.drop 396) (PairLightPrepared8.leftRows.drop 396)
    · exact left_prefix_005_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0417
  have h0376 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 151
      (PairLightPrepared8.leftCached.drop 376) (PairLightPrepared8.leftRows.drop 376) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 20 131
      (PairLightPrepared8.leftCached.drop 376) (PairLightPrepared8.leftRows.drop 376)
    · exact left_prefix_005_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0396
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, leftCached004, leftRows004, leftCached005, leftRows005, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0376

end D1Bound5.PairLightAdaptivePrepared8
end
