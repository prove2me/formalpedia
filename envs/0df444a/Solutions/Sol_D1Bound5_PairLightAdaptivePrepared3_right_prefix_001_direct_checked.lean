-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:19:18.445778+00:00
-- url     : https://prove2.me/submissions/f692627c-bc31-445b-90b7-0908700f359c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_001_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 195
      (PairLightPrepared3.rightCached.drop 111) (PairLightPrepared3.rightRows.drop 111) = true := by
  have h303 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 3
      (PairLightPrepared3.rightCached.drop 303) (PairLightPrepared3.rightRows.drop 303) = true := right_prefix_001_part08_checked
  have h279 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 27
      (PairLightPrepared3.rightCached.drop 279) (PairLightPrepared3.rightRows.drop 279) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 3
      (PairLightPrepared3.rightCached.drop 279) (PairLightPrepared3.rightRows.drop 279)
    · exact right_prefix_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h303
  have h255 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 51
      (PairLightPrepared3.rightCached.drop 255) (PairLightPrepared3.rightRows.drop 255) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 27
      (PairLightPrepared3.rightCached.drop 255) (PairLightPrepared3.rightRows.drop 255)
    · exact right_prefix_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h279
  have h231 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 75
      (PairLightPrepared3.rightCached.drop 231) (PairLightPrepared3.rightRows.drop 231) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 51
      (PairLightPrepared3.rightCached.drop 231) (PairLightPrepared3.rightRows.drop 231)
    · exact right_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h255
  have h207 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 99
      (PairLightPrepared3.rightCached.drop 207) (PairLightPrepared3.rightRows.drop 207) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 75
      (PairLightPrepared3.rightCached.drop 207) (PairLightPrepared3.rightRows.drop 207)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h231
  have h183 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 123
      (PairLightPrepared3.rightCached.drop 183) (PairLightPrepared3.rightRows.drop 183) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 99
      (PairLightPrepared3.rightCached.drop 183) (PairLightPrepared3.rightRows.drop 183)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h207
  have h159 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 147
      (PairLightPrepared3.rightCached.drop 159) (PairLightPrepared3.rightRows.drop 159) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 123
      (PairLightPrepared3.rightCached.drop 159) (PairLightPrepared3.rightRows.drop 159)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h183
  have h135 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 171
      (PairLightPrepared3.rightCached.drop 135) (PairLightPrepared3.rightRows.drop 135) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 147
      (PairLightPrepared3.rightCached.drop 135) (PairLightPrepared3.rightRows.drop 135)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h159
  have h111 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 195
      (PairLightPrepared3.rightCached.drop 111) (PairLightPrepared3.rightRows.drop 111) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 171
      (PairLightPrepared3.rightCached.drop 111) (PairLightPrepared3.rightRows.drop 111)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h135
  exact h111
end D1Bound5.PairLightAdaptivePrepared3
end
