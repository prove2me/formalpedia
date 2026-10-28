-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:29.942728+00:00
-- url     : https://prove2.me/submissions/4f2e4a43-a41e-42b7-814d-6379eb809883

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 71
      rightCached002 rightRows002 = true := by
  have h0179 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 13
      (PairLightPrepared8.rightCached.drop 179) (PairLightPrepared8.rightRows.drop 179) = true := right_prefix_002_part05_checked
  have h0167 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 25
      (PairLightPrepared8.rightCached.drop 167) (PairLightPrepared8.rightRows.drop 167) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 13
      (PairLightPrepared8.rightCached.drop 167) (PairLightPrepared8.rightRows.drop 167)
    · exact right_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0179
  have h0155 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 37
      (PairLightPrepared8.rightCached.drop 155) (PairLightPrepared8.rightRows.drop 155) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 25
      (PairLightPrepared8.rightCached.drop 155) (PairLightPrepared8.rightRows.drop 155)
    · exact right_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0167
  have h0143 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 49
      (PairLightPrepared8.rightCached.drop 143) (PairLightPrepared8.rightRows.drop 143) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 37
      (PairLightPrepared8.rightCached.drop 143) (PairLightPrepared8.rightRows.drop 143)
    · exact right_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0155
  have h0132 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 60
      (PairLightPrepared8.rightCached.drop 132) (PairLightPrepared8.rightRows.drop 132) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 11 49
      (PairLightPrepared8.rightCached.drop 132) (PairLightPrepared8.rightRows.drop 132)
    · exact right_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0143
  have h0121 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 71
      (PairLightPrepared8.rightCached.drop 121) (PairLightPrepared8.rightRows.drop 121) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 11 60
      (PairLightPrepared8.rightCached.drop 121) (PairLightPrepared8.rightRows.drop 121)
    · exact right_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0132
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0121

end D1Bound5.PairLightAdaptivePrepared8
end
