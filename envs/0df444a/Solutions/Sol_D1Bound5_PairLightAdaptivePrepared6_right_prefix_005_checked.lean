-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:37:35.086175+00:00
-- url     : https://prove2.me/submissions/665e5ef1-8a53-458e-aa77-e5406e02688f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_005_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 181
      rightCached005 rightRows005 = true := by
  have h0638 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 19
      (PairLightPrepared6.rightCached.drop 638) (PairLightPrepared6.rightRows.drop 638) = true := right_prefix_005_part03_checked
  have h0563 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 94
      (PairLightPrepared6.rightCached.drop 563) (PairLightPrepared6.rightRows.drop 563) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 75 19
      (PairLightPrepared6.rightCached.drop 563) (PairLightPrepared6.rightRows.drop 563)
    · exact right_prefix_005_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0638
  have h0514 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 143
      (PairLightPrepared6.rightCached.drop 514) (PairLightPrepared6.rightRows.drop 514) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 49 94
      (PairLightPrepared6.rightCached.drop 514) (PairLightPrepared6.rightRows.drop 514)
    · exact right_prefix_005_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0563
  have h0476 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 181
      (PairLightPrepared6.rightCached.drop 476) (PairLightPrepared6.rightRows.drop 476) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 38 143
      (PairLightPrepared6.rightCached.drop 476) (PairLightPrepared6.rightRows.drop 476)
    · exact right_prefix_005_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0514
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, rightCached003, rightRows003, rightCached004, rightRows004, rightCached005, rightRows005, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0476

end D1Bound5.PairLightAdaptivePrepared6
end
