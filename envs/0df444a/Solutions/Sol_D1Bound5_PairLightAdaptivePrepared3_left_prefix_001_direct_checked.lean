-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:28.340426+00:00
-- url     : https://prove2.me/submissions/a0ee06d8-3df2-43e0-94f7-2d3fddcd3aec

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_001_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 199
      (PairLightPrepared3.leftCached.drop 112) (PairLightPrepared3.leftRows.drop 112) = true := by
  have h304 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 7
      (PairLightPrepared3.leftCached.drop 304) (PairLightPrepared3.leftRows.drop 304) = true := left_prefix_001_part08_checked
  have h280 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 31
      (PairLightPrepared3.leftCached.drop 280) (PairLightPrepared3.leftRows.drop 280) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 7
      (PairLightPrepared3.leftCached.drop 280) (PairLightPrepared3.leftRows.drop 280)
    · exact left_prefix_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h304
  have h256 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 55
      (PairLightPrepared3.leftCached.drop 256) (PairLightPrepared3.leftRows.drop 256) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 31
      (PairLightPrepared3.leftCached.drop 256) (PairLightPrepared3.leftRows.drop 256)
    · exact left_prefix_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h280
  have h232 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 79
      (PairLightPrepared3.leftCached.drop 232) (PairLightPrepared3.leftRows.drop 232) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 55
      (PairLightPrepared3.leftCached.drop 232) (PairLightPrepared3.leftRows.drop 232)
    · exact left_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h256
  have h208 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 103
      (PairLightPrepared3.leftCached.drop 208) (PairLightPrepared3.leftRows.drop 208) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 79
      (PairLightPrepared3.leftCached.drop 208) (PairLightPrepared3.leftRows.drop 208)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h232
  have h184 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 127
      (PairLightPrepared3.leftCached.drop 184) (PairLightPrepared3.leftRows.drop 184) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 103
      (PairLightPrepared3.leftCached.drop 184) (PairLightPrepared3.leftRows.drop 184)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h208
  have h160 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 151
      (PairLightPrepared3.leftCached.drop 160) (PairLightPrepared3.leftRows.drop 160) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 127
      (PairLightPrepared3.leftCached.drop 160) (PairLightPrepared3.leftRows.drop 160)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h184
  have h136 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 175
      (PairLightPrepared3.leftCached.drop 136) (PairLightPrepared3.leftRows.drop 136) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 151
      (PairLightPrepared3.leftCached.drop 136) (PairLightPrepared3.leftRows.drop 136)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h160
  have h112 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 199
      (PairLightPrepared3.leftCached.drop 112) (PairLightPrepared3.leftRows.drop 112) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 175
      (PairLightPrepared3.leftCached.drop 112) (PairLightPrepared3.leftRows.drop 112)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h136
  exact h112
end D1Bound5.PairLightAdaptivePrepared3
end
