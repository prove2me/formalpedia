-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:32.171803+00:00
-- url     : https://prove2.me/submissions/43d32c2b-fbda-4fc5-87ba-6282f751a0b6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_pilot12_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_000_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 101
      (PairLightPrepared19.rightCached.drop 0) (PairLightPrepared19.rightRows.drop 0) = true := by
  have h096 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 5
      (PairLightPrepared19.rightCached.drop 96) (PairLightPrepared19.rightRows.drop 96) = true := right_prefix_000_part08_checked
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 17
      (PairLightPrepared19.rightCached.drop 84) (PairLightPrepared19.rightRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 5
      (PairLightPrepared19.rightCached.drop 84) (PairLightPrepared19.rightRows.drop 84)
    · exact right_prefix_000_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h096
  have h072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 29
      (PairLightPrepared19.rightCached.drop 72) (PairLightPrepared19.rightRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 17
      (PairLightPrepared19.rightCached.drop 72) (PairLightPrepared19.rightRows.drop 72)
    · exact right_prefix_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 41
      (PairLightPrepared19.rightCached.drop 60) (PairLightPrepared19.rightRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 29
      (PairLightPrepared19.rightCached.drop 60) (PairLightPrepared19.rightRows.drop 60)
    · exact right_prefix_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 53
      (PairLightPrepared19.rightCached.drop 48) (PairLightPrepared19.rightRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 41
      (PairLightPrepared19.rightCached.drop 48) (PairLightPrepared19.rightRows.drop 48)
    · exact right_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 65
      (PairLightPrepared19.rightCached.drop 36) (PairLightPrepared19.rightRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 53
      (PairLightPrepared19.rightCached.drop 36) (PairLightPrepared19.rightRows.drop 36)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 77
      (PairLightPrepared19.rightCached.drop 24) (PairLightPrepared19.rightRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 65
      (PairLightPrepared19.rightCached.drop 24) (PairLightPrepared19.rightRows.drop 24)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 89
      (PairLightPrepared19.rightCached.drop 12) (PairLightPrepared19.rightRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 77
      (PairLightPrepared19.rightCached.drop 12) (PairLightPrepared19.rightRows.drop 12)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 101
      (PairLightPrepared19.rightCached.drop 0) (PairLightPrepared19.rightRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 12 89
      (PairLightPrepared19.rightCached.drop 0) (PairLightPrepared19.rightRows.drop 0)
    · exact right_pilot12_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h012
  exact h000
end D1Bound5.PairLightAdaptivePrepared19
end
