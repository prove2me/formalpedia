-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:08.150214+00:00
-- url     : https://prove2.me/submissions/1ed421d5-47ae-4c0c-a79b-1675b8473365

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_003_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 150
      leftCached003 leftRows003 = true := by
  have h0402 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 3
      (PairLightPrepared10.leftCached.drop 402) (PairLightPrepared10.leftRows.drop 402) = true := left_prefix_003_part06_checked
  have h0371 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 34
      (PairLightPrepared10.leftCached.drop 371) (PairLightPrepared10.leftRows.drop 371) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 31 3
      (PairLightPrepared10.leftCached.drop 371) (PairLightPrepared10.leftRows.drop 371)
    · exact left_prefix_003_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0402
  have h0344 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 61
      (PairLightPrepared10.leftCached.drop 344) (PairLightPrepared10.leftRows.drop 344) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 27 34
      (PairLightPrepared10.leftCached.drop 344) (PairLightPrepared10.leftRows.drop 344)
    · exact left_prefix_003_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0371
  have h0319 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 86
      (PairLightPrepared10.leftCached.drop 319) (PairLightPrepared10.leftRows.drop 319) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 25 61
      (PairLightPrepared10.leftCached.drop 319) (PairLightPrepared10.leftRows.drop 319)
    · exact left_prefix_003_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0344
  have h0296 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 109
      (PairLightPrepared10.leftCached.drop 296) (PairLightPrepared10.leftRows.drop 296) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 23 86
      (PairLightPrepared10.leftCached.drop 296) (PairLightPrepared10.leftRows.drop 296)
    · exact left_prefix_003_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0319
  have h0275 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 130
      (PairLightPrepared10.leftCached.drop 275) (PairLightPrepared10.leftRows.drop 275) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 21 109
      (PairLightPrepared10.leftCached.drop 275) (PairLightPrepared10.leftRows.drop 275)
    · exact left_prefix_003_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0296
  have h0255 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 150
      (PairLightPrepared10.leftCached.drop 255) (PairLightPrepared10.leftRows.drop 255) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 20 130
      (PairLightPrepared10.leftCached.drop 255) (PairLightPrepared10.leftRows.drop 255)
    · exact left_prefix_003_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0275
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0255

end D1Bound5.PairLightAdaptivePrepared10
end
