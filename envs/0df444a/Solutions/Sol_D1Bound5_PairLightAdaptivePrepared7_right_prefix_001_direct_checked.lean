-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:45.404327+00:00
-- url     : https://prove2.me/submissions/04992545-177c-4bcb-b559-f892d3eae581

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 166
      (PairLightPrepared7.rightCached.drop 106) (PairLightPrepared7.rightRows.drop 106) = true := by
  have h250 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 22
      (PairLightPrepared7.rightCached.drop 250) (PairLightPrepared7.rightRows.drop 250) = true := right_prefix_001_part06_checked
  have h226 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 46
      (PairLightPrepared7.rightCached.drop 226) (PairLightPrepared7.rightRows.drop 226) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 22
      (PairLightPrepared7.rightCached.drop 226) (PairLightPrepared7.rightRows.drop 226)
    · exact right_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h250
  have h202 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 70
      (PairLightPrepared7.rightCached.drop 202) (PairLightPrepared7.rightRows.drop 202) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 46
      (PairLightPrepared7.rightCached.drop 202) (PairLightPrepared7.rightRows.drop 202)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h226
  have h178 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 94
      (PairLightPrepared7.rightCached.drop 178) (PairLightPrepared7.rightRows.drop 178) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 70
      (PairLightPrepared7.rightCached.drop 178) (PairLightPrepared7.rightRows.drop 178)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h202
  have h154 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 118
      (PairLightPrepared7.rightCached.drop 154) (PairLightPrepared7.rightRows.drop 154) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 94
      (PairLightPrepared7.rightCached.drop 154) (PairLightPrepared7.rightRows.drop 154)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h178
  have h130 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 142
      (PairLightPrepared7.rightCached.drop 130) (PairLightPrepared7.rightRows.drop 130) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 118
      (PairLightPrepared7.rightCached.drop 130) (PairLightPrepared7.rightRows.drop 130)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h154
  have h106 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 166
      (PairLightPrepared7.rightCached.drop 106) (PairLightPrepared7.rightRows.drop 106) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 142
      (PairLightPrepared7.rightCached.drop 106) (PairLightPrepared7.rightRows.drop 106)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h130
  exact h106
end D1Bound5.PairLightAdaptivePrepared7
end
