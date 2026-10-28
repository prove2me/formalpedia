-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:42.606227+00:00
-- url     : https://prove2.me/submissions/638c489e-e863-4258-9513-7b7c4dbcfbd1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_003_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 103
      rightCached003 rightRows003 = true := by
  have h0320 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 1
      (PairLightPrepared6.rightCached.drop 320) (PairLightPrepared6.rightRows.drop 320) = true := right_prefix_003_part06_checked
  have h0301 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 20
      (PairLightPrepared6.rightCached.drop 301) (PairLightPrepared6.rightRows.drop 301) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 19 1
      (PairLightPrepared6.rightCached.drop 301) (PairLightPrepared6.rightRows.drop 301)
    · exact right_prefix_003_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0320
  have h0283 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 38
      (PairLightPrepared6.rightCached.drop 283) (PairLightPrepared6.rightRows.drop 283) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 18 20
      (PairLightPrepared6.rightCached.drop 283) (PairLightPrepared6.rightRows.drop 283)
    · exact right_prefix_003_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0301
  have h0266 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 55
      (PairLightPrepared6.rightCached.drop 266) (PairLightPrepared6.rightRows.drop 266) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 17 38
      (PairLightPrepared6.rightCached.drop 266) (PairLightPrepared6.rightRows.drop 266)
    · exact right_prefix_003_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0283
  have h0249 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 72
      (PairLightPrepared6.rightCached.drop 249) (PairLightPrepared6.rightRows.drop 249) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 17 55
      (PairLightPrepared6.rightCached.drop 249) (PairLightPrepared6.rightRows.drop 249)
    · exact right_prefix_003_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0266
  have h0233 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 88
      (PairLightPrepared6.rightCached.drop 233) (PairLightPrepared6.rightRows.drop 233) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 16 72
      (PairLightPrepared6.rightCached.drop 233) (PairLightPrepared6.rightRows.drop 233)
    · exact right_prefix_003_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0249
  have h0218 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 103
      (PairLightPrepared6.rightCached.drop 218) (PairLightPrepared6.rightRows.drop 218) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 15 88
      (PairLightPrepared6.rightCached.drop 218) (PairLightPrepared6.rightRows.drop 218)
    · exact right_prefix_003_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0233
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, rightCached003, rightRows003, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0218

end D1Bound5.PairLightAdaptivePrepared6
end
