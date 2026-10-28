-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:39.040418+00:00
-- url     : https://prove2.me/submissions/c76f5754-2d06-4c5b-85d9-89e7e1a4121b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_pilot12_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part09_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 112
      (PairLightPrepared3.leftCached.drop 0) (PairLightPrepared3.leftRows.drop 0) = true := by
  have h108 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 4
      (PairLightPrepared3.leftCached.drop 108) (PairLightPrepared3.leftRows.drop 108) = true := left_prefix_000_part09_checked
  have h096 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 16
      (PairLightPrepared3.leftCached.drop 96) (PairLightPrepared3.leftRows.drop 96) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 4
      (PairLightPrepared3.leftCached.drop 96) (PairLightPrepared3.leftRows.drop 96)
    · exact left_prefix_000_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h108
  have h084 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 28
      (PairLightPrepared3.leftCached.drop 84) (PairLightPrepared3.leftRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 16
      (PairLightPrepared3.leftCached.drop 84) (PairLightPrepared3.leftRows.drop 84)
    · exact left_prefix_000_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h096
  have h072 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 40
      (PairLightPrepared3.leftCached.drop 72) (PairLightPrepared3.leftRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 28
      (PairLightPrepared3.leftCached.drop 72) (PairLightPrepared3.leftRows.drop 72)
    · exact left_prefix_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h060 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 52
      (PairLightPrepared3.leftCached.drop 60) (PairLightPrepared3.leftRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 40
      (PairLightPrepared3.leftCached.drop 60) (PairLightPrepared3.leftRows.drop 60)
    · exact left_prefix_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h072
  have h048 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 64
      (PairLightPrepared3.leftCached.drop 48) (PairLightPrepared3.leftRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 52
      (PairLightPrepared3.leftCached.drop 48) (PairLightPrepared3.leftRows.drop 48)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h060
  have h036 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 76
      (PairLightPrepared3.leftCached.drop 36) (PairLightPrepared3.leftRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 64
      (PairLightPrepared3.leftCached.drop 36) (PairLightPrepared3.leftRows.drop 36)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h048
  have h024 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 88
      (PairLightPrepared3.leftCached.drop 24) (PairLightPrepared3.leftRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 76
      (PairLightPrepared3.leftCached.drop 24) (PairLightPrepared3.leftRows.drop 24)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h012 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 100
      (PairLightPrepared3.leftCached.drop 12) (PairLightPrepared3.leftRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 88
      (PairLightPrepared3.leftCached.drop 12) (PairLightPrepared3.leftRows.drop 12)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 112
      (PairLightPrepared3.leftCached.drop 0) (PairLightPrepared3.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 12 100
      (PairLightPrepared3.leftCached.drop 0) (PairLightPrepared3.leftRows.drop 0)
    · exact left_pilot12_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h012
  exact h000
end D1Bound5.PairLightAdaptivePrepared3
end
