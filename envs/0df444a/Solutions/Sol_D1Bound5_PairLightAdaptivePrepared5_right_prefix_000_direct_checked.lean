-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:27.342656+00:00
-- url     : https://prove2.me/submissions/a24aca2e-2b5f-4b1d-8eac-e2be5f1aa264

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_pilot12_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_right_prefix_000_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 106
      (PairLightPrepared5.rightCached.drop 0) (PairLightPrepared5.rightRows.drop 0) = true := by
  have h096 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 10
      (PairLightPrepared5.rightCached.drop 96) (PairLightPrepared5.rightRows.drop 96) = true := right_prefix_000_part08_checked
  have h084 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 22
      (PairLightPrepared5.rightCached.drop 84) (PairLightPrepared5.rightRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 10
      (PairLightPrepared5.rightCached.drop 84) (PairLightPrepared5.rightRows.drop 84)
    · exact right_prefix_000_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h096
  have h072 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 34
      (PairLightPrepared5.rightCached.drop 72) (PairLightPrepared5.rightRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 22
      (PairLightPrepared5.rightCached.drop 72) (PairLightPrepared5.rightRows.drop 72)
    · exact right_prefix_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h060 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 46
      (PairLightPrepared5.rightCached.drop 60) (PairLightPrepared5.rightRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 34
      (PairLightPrepared5.rightCached.drop 60) (PairLightPrepared5.rightRows.drop 60)
    · exact right_prefix_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h072
  have h048 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 58
      (PairLightPrepared5.rightCached.drop 48) (PairLightPrepared5.rightRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 46
      (PairLightPrepared5.rightCached.drop 48) (PairLightPrepared5.rightRows.drop 48)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h060
  have h036 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 70
      (PairLightPrepared5.rightCached.drop 36) (PairLightPrepared5.rightRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 58
      (PairLightPrepared5.rightCached.drop 36) (PairLightPrepared5.rightRows.drop 36)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h048
  have h024 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 82
      (PairLightPrepared5.rightCached.drop 24) (PairLightPrepared5.rightRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 70
      (PairLightPrepared5.rightCached.drop 24) (PairLightPrepared5.rightRows.drop 24)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h012 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 94
      (PairLightPrepared5.rightCached.drop 12) (PairLightPrepared5.rightRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 82
      (PairLightPrepared5.rightCached.drop 12) (PairLightPrepared5.rightRows.drop 12)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 106
      (PairLightPrepared5.rightCached.drop 0) (PairLightPrepared5.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 12 94
      (PairLightPrepared5.rightCached.drop 0) (PairLightPrepared5.rightRows.drop 0)
    · exact right_pilot12_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h012
  exact h000
end D1Bound5.PairLightAdaptivePrepared5
end
