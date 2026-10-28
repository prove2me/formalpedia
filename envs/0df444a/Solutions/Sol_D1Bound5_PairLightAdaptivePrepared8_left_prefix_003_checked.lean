-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:25.671671+00:00
-- url     : https://prove2.me/submissions/a029de52-6f41-4dcf-b0a0-f93ba137b6a6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_003_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 82
      leftCached003 leftRows003 = true := by
  have h0260 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.leftCached.drop 260) (PairLightPrepared8.leftRows.drop 260) = true := left_prefix_003_part05_checked
  have h0246 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 28
      (PairLightPrepared8.leftCached.drop 246) (PairLightPrepared8.leftRows.drop 246) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 14 14
      (PairLightPrepared8.leftCached.drop 246) (PairLightPrepared8.leftRows.drop 246)
    · exact left_prefix_003_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0260
  have h0232 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 42
      (PairLightPrepared8.leftCached.drop 232) (PairLightPrepared8.leftRows.drop 232) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 14 28
      (PairLightPrepared8.leftCached.drop 232) (PairLightPrepared8.leftRows.drop 232)
    · exact left_prefix_003_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0246
  have h0218 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 56
      (PairLightPrepared8.leftCached.drop 218) (PairLightPrepared8.leftRows.drop 218) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 14 42
      (PairLightPrepared8.leftCached.drop 218) (PairLightPrepared8.leftRows.drop 218)
    · exact left_prefix_003_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0232
  have h0205 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 69
      (PairLightPrepared8.leftCached.drop 205) (PairLightPrepared8.leftRows.drop 205) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 13 56
      (PairLightPrepared8.leftCached.drop 205) (PairLightPrepared8.leftRows.drop 205)
    · exact left_prefix_003_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0218
  have h0192 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 82
      (PairLightPrepared8.leftCached.drop 192) (PairLightPrepared8.leftRows.drop 192) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 13 69
      (PairLightPrepared8.leftCached.drop 192) (PairLightPrepared8.leftRows.drop 192)
    · exact left_prefix_003_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0205
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0192

end D1Bound5.PairLightAdaptivePrepared8
end
