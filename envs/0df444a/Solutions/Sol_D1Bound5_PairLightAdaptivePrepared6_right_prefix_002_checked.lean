-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:28:28.402986+00:00
-- url     : https://prove2.me/submissions/9811788a-db26-4a0d-95eb-c16c6cd03681

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 83
      rightCached002 rightRows002 = true := by
  have h0203 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 15
      (PairLightPrepared6.rightCached.drop 203) (PairLightPrepared6.rightRows.drop 203) = true := right_prefix_002_part05_checked
  have h0189 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 29
      (PairLightPrepared6.rightCached.drop 189) (PairLightPrepared6.rightRows.drop 189) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 14 15
      (PairLightPrepared6.rightCached.drop 189) (PairLightPrepared6.rightRows.drop 189)
    · exact right_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0203
  have h0175 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 43
      (PairLightPrepared6.rightCached.drop 175) (PairLightPrepared6.rightRows.drop 175) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 14 29
      (PairLightPrepared6.rightCached.drop 175) (PairLightPrepared6.rightRows.drop 175)
    · exact right_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0189
  have h0161 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 57
      (PairLightPrepared6.rightCached.drop 161) (PairLightPrepared6.rightRows.drop 161) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 14 43
      (PairLightPrepared6.rightCached.drop 161) (PairLightPrepared6.rightRows.drop 161)
    · exact right_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0175
  have h0148 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 70
      (PairLightPrepared6.rightCached.drop 148) (PairLightPrepared6.rightRows.drop 148) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 13 57
      (PairLightPrepared6.rightCached.drop 148) (PairLightPrepared6.rightRows.drop 148)
    · exact right_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0161
  have h0135 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 83
      (PairLightPrepared6.rightCached.drop 135) (PairLightPrepared6.rightRows.drop 135) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 13 70
      (PairLightPrepared6.rightCached.drop 135) (PairLightPrepared6.rightRows.drop 135)
    · exact right_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0148
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0135

end D1Bound5.PairLightAdaptivePrepared6
end
