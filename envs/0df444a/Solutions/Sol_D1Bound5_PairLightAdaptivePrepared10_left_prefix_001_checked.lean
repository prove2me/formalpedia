-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:30:42.175993+00:00
-- url     : https://prove2.me/submissions/ced2131d-e290-4750-9d1f-cf22e41ea179

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 82
      leftCached001 leftRows001 = true := by
  have h0139 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 14
      (PairLightPrepared10.leftCached.drop 139) (PairLightPrepared10.leftRows.drop 139) = true := left_prefix_001_part05_checked
  have h0125 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 28
      (PairLightPrepared10.leftCached.drop 125) (PairLightPrepared10.leftRows.drop 125) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 14 14
      (PairLightPrepared10.leftCached.drop 125) (PairLightPrepared10.leftRows.drop 125)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0139
  have h0111 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 42
      (PairLightPrepared10.leftCached.drop 111) (PairLightPrepared10.leftRows.drop 111) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 14 28
      (PairLightPrepared10.leftCached.drop 111) (PairLightPrepared10.leftRows.drop 111)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0125
  have h0097 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 56
      (PairLightPrepared10.leftCached.drop 97) (PairLightPrepared10.leftRows.drop 97) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 14 42
      (PairLightPrepared10.leftCached.drop 97) (PairLightPrepared10.leftRows.drop 97)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0111
  have h0084 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 69
      (PairLightPrepared10.leftCached.drop 84) (PairLightPrepared10.leftRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 13 56
      (PairLightPrepared10.leftCached.drop 84) (PairLightPrepared10.leftRows.drop 84)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0097
  have h0071 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 82
      (PairLightPrepared10.leftCached.drop 71) (PairLightPrepared10.leftRows.drop 71) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 13 69
      (PairLightPrepared10.leftCached.drop 71) (PairLightPrepared10.leftRows.drop 71)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0084
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0071

end D1Bound5.PairLightAdaptivePrepared10
end
