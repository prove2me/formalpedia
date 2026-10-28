-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:43.598177+00:00
-- url     : https://prove2.me/submissions/10d2a529-1c32-4958-a0f8-9d3e042b58d8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_pilot12_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 97
      (PairLightPrepared39.leftCached.drop 0) (PairLightPrepared39.leftRows.drop 0) = true := by
  have h096 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 1
      (PairLightPrepared39.leftCached.drop 96) (PairLightPrepared39.leftRows.drop 96) = true := left_prefix_000_part08_checked
  have h084 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 13
      (PairLightPrepared39.leftCached.drop 84) (PairLightPrepared39.leftRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 1
      (PairLightPrepared39.leftCached.drop 84) (PairLightPrepared39.leftRows.drop 84)
    · exact left_prefix_000_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h096
  have h072 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 25
      (PairLightPrepared39.leftCached.drop 72) (PairLightPrepared39.leftRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 13
      (PairLightPrepared39.leftCached.drop 72) (PairLightPrepared39.leftRows.drop 72)
    · exact left_prefix_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 37
      (PairLightPrepared39.leftCached.drop 60) (PairLightPrepared39.leftRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 25
      (PairLightPrepared39.leftCached.drop 60) (PairLightPrepared39.leftRows.drop 60)
    · exact left_prefix_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 49
      (PairLightPrepared39.leftCached.drop 48) (PairLightPrepared39.leftRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 37
      (PairLightPrepared39.leftCached.drop 48) (PairLightPrepared39.leftRows.drop 48)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 61
      (PairLightPrepared39.leftCached.drop 36) (PairLightPrepared39.leftRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 49
      (PairLightPrepared39.leftCached.drop 36) (PairLightPrepared39.leftRows.drop 36)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 73
      (PairLightPrepared39.leftCached.drop 24) (PairLightPrepared39.leftRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 61
      (PairLightPrepared39.leftCached.drop 24) (PairLightPrepared39.leftRows.drop 24)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 85
      (PairLightPrepared39.leftCached.drop 12) (PairLightPrepared39.leftRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 73
      (PairLightPrepared39.leftCached.drop 12) (PairLightPrepared39.leftRows.drop 12)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 97
      (PairLightPrepared39.leftCached.drop 0) (PairLightPrepared39.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 12 85
      (PairLightPrepared39.leftCached.drop 0) (PairLightPrepared39.leftRows.drop 0)
    · exact left_pilot12_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h012
  exact h000
end D1Bound5.PairLightAdaptivePrepared39
end
