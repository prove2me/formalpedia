-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:37.486601+00:00
-- url     : https://prove2.me/submissions/1f3eedbf-a938-4819-92d1-1bc50a86dd34

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 92
      (PairLightPrepared43.rightCached.drop 0) (PairLightPrepared43.rightRows.drop 0) = true := by
  have h084 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 8
      (PairLightPrepared43.rightCached.drop 84) (PairLightPrepared43.rightRows.drop 84) = true := right_prefix_000_part07_checked
  have h072 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 20
      (PairLightPrepared43.rightCached.drop 72) (PairLightPrepared43.rightRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 8
      (PairLightPrepared43.rightCached.drop 72) (PairLightPrepared43.rightRows.drop 72)
    · exact right_prefix_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 32
      (PairLightPrepared43.rightCached.drop 60) (PairLightPrepared43.rightRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 20
      (PairLightPrepared43.rightCached.drop 60) (PairLightPrepared43.rightRows.drop 60)
    · exact right_prefix_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 44
      (PairLightPrepared43.rightCached.drop 48) (PairLightPrepared43.rightRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 32
      (PairLightPrepared43.rightCached.drop 48) (PairLightPrepared43.rightRows.drop 48)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 56
      (PairLightPrepared43.rightCached.drop 36) (PairLightPrepared43.rightRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 44
      (PairLightPrepared43.rightCached.drop 36) (PairLightPrepared43.rightRows.drop 36)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 68
      (PairLightPrepared43.rightCached.drop 24) (PairLightPrepared43.rightRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 56
      (PairLightPrepared43.rightCached.drop 24) (PairLightPrepared43.rightRows.drop 24)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 80
      (PairLightPrepared43.rightCached.drop 12) (PairLightPrepared43.rightRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 68
      (PairLightPrepared43.rightCached.drop 12) (PairLightPrepared43.rightRows.drop 12)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 92
      (PairLightPrepared43.rightCached.drop 0) (PairLightPrepared43.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 80
      (PairLightPrepared43.rightCached.drop 0) (PairLightPrepared43.rightRows.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h012
  exact h000
end D1Bound5.PairLightAdaptivePrepared43
end
