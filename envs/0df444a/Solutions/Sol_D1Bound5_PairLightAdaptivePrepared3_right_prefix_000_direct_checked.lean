-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.right_prefix_000_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:17.120396+00:00
-- url     : https://prove2.me/submissions/1eb65f58-ba66-48fe-94e4-cedab83d3834

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_pilot12_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_prefix_000_part09_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 111
      (PairLightPrepared3.rightCached.drop 0) (PairLightPrepared3.rightRows.drop 0) = true := by
  have h108 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 3
      (PairLightPrepared3.rightCached.drop 108) (PairLightPrepared3.rightRows.drop 108) = true := right_prefix_000_part09_checked
  have h096 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 15
      (PairLightPrepared3.rightCached.drop 96) (PairLightPrepared3.rightRows.drop 96) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 3
      (PairLightPrepared3.rightCached.drop 96) (PairLightPrepared3.rightRows.drop 96)
    · exact right_prefix_000_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h108
  have h084 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 27
      (PairLightPrepared3.rightCached.drop 84) (PairLightPrepared3.rightRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 15
      (PairLightPrepared3.rightCached.drop 84) (PairLightPrepared3.rightRows.drop 84)
    · exact right_prefix_000_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h096
  have h072 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 39
      (PairLightPrepared3.rightCached.drop 72) (PairLightPrepared3.rightRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 27
      (PairLightPrepared3.rightCached.drop 72) (PairLightPrepared3.rightRows.drop 72)
    · exact right_prefix_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h060 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 51
      (PairLightPrepared3.rightCached.drop 60) (PairLightPrepared3.rightRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 39
      (PairLightPrepared3.rightCached.drop 60) (PairLightPrepared3.rightRows.drop 60)
    · exact right_prefix_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h072
  have h048 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 63
      (PairLightPrepared3.rightCached.drop 48) (PairLightPrepared3.rightRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 51
      (PairLightPrepared3.rightCached.drop 48) (PairLightPrepared3.rightRows.drop 48)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h060
  have h036 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 75
      (PairLightPrepared3.rightCached.drop 36) (PairLightPrepared3.rightRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 63
      (PairLightPrepared3.rightCached.drop 36) (PairLightPrepared3.rightRows.drop 36)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h048
  have h024 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 87
      (PairLightPrepared3.rightCached.drop 24) (PairLightPrepared3.rightRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 75
      (PairLightPrepared3.rightCached.drop 24) (PairLightPrepared3.rightRows.drop 24)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h012 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 99
      (PairLightPrepared3.rightCached.drop 12) (PairLightPrepared3.rightRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 87
      (PairLightPrepared3.rightCached.drop 12) (PairLightPrepared3.rightRows.drop 12)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 111
      (PairLightPrepared3.rightCached.drop 0) (PairLightPrepared3.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 99
      (PairLightPrepared3.rightCached.drop 0) (PairLightPrepared3.rightRows.drop 0)
    · exact right_pilot12_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h012
  exact h000
end D1Bound5.PairLightAdaptivePrepared3
end
