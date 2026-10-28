-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:28.361879+00:00
-- url     : https://prove2.me/submissions/cd55c01d-1882-4c61-ae34-1913cff17b44

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 136
      (PairLightPrepared39.leftCached.drop 97) (PairLightPrepared39.leftRows.drop 97) = true := by
  have h217 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 16
      (PairLightPrepared39.leftCached.drop 217) (PairLightPrepared39.leftRows.drop 217) = true := left_prefix_001_part05_checked
  have h193 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 40
      (PairLightPrepared39.leftCached.drop 193) (PairLightPrepared39.leftRows.drop 193) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 16
      (PairLightPrepared39.leftCached.drop 193) (PairLightPrepared39.leftRows.drop 193)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h217
  have h169 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 64
      (PairLightPrepared39.leftCached.drop 169) (PairLightPrepared39.leftRows.drop 169) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 40
      (PairLightPrepared39.leftCached.drop 169) (PairLightPrepared39.leftRows.drop 169)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h193
  have h145 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 88
      (PairLightPrepared39.leftCached.drop 145) (PairLightPrepared39.leftRows.drop 145) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 64
      (PairLightPrepared39.leftCached.drop 145) (PairLightPrepared39.leftRows.drop 145)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h169
  have h121 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 112
      (PairLightPrepared39.leftCached.drop 121) (PairLightPrepared39.leftRows.drop 121) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 88
      (PairLightPrepared39.leftCached.drop 121) (PairLightPrepared39.leftRows.drop 121)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h145
  have h097 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 136
      (PairLightPrepared39.leftCached.drop 97) (PairLightPrepared39.leftRows.drop 97) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 112
      (PairLightPrepared39.leftCached.drop 97) (PairLightPrepared39.leftRows.drop 97)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h121
  exact h097
end D1Bound5.PairLightAdaptivePrepared39
end
