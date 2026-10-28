-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:13.762841+00:00
-- url     : https://prove2.me/submissions/417b1d5f-01d6-4063-9cff-e5608eeb705d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_004_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 102
      leftCached004 leftRows004 = true := by
  have h0357 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 19
      (PairLightPrepared8.leftCached.drop 357) (PairLightPrepared8.leftRows.drop 357) = true := left_prefix_004_part05_checked
  have h0339 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 37
      (PairLightPrepared8.leftCached.drop 339) (PairLightPrepared8.leftRows.drop 339) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 18 19
      (PairLightPrepared8.leftCached.drop 339) (PairLightPrepared8.leftRows.drop 339)
    · exact left_prefix_004_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0357
  have h0322 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 54
      (PairLightPrepared8.leftCached.drop 322) (PairLightPrepared8.leftRows.drop 322) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 17 37
      (PairLightPrepared8.leftCached.drop 322) (PairLightPrepared8.leftRows.drop 322)
    · exact left_prefix_004_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0339
  have h0305 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 71
      (PairLightPrepared8.leftCached.drop 305) (PairLightPrepared8.leftRows.drop 305) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 17 54
      (PairLightPrepared8.leftCached.drop 305) (PairLightPrepared8.leftRows.drop 305)
    · exact left_prefix_004_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0322
  have h0289 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 87
      (PairLightPrepared8.leftCached.drop 289) (PairLightPrepared8.leftRows.drop 289) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 16 71
      (PairLightPrepared8.leftCached.drop 289) (PairLightPrepared8.leftRows.drop 289)
    · exact left_prefix_004_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0305
  have h0274 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 102
      (PairLightPrepared8.leftCached.drop 274) (PairLightPrepared8.leftRows.drop 274) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 15 87
      (PairLightPrepared8.leftCached.drop 274) (PairLightPrepared8.leftRows.drop 274)
    · exact left_prefix_004_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0289
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, leftCached004, leftRows004, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0274

end D1Bound5.PairLightAdaptivePrepared8
end
