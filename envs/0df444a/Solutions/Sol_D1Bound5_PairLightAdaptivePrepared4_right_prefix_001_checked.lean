-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:19:21.433012+00:00
-- url     : https://prove2.me/submissions/fc076bdb-1664-42ee-9988-324e2837d004

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 82
      rightCached001 rightRows001 = true := by
  have h0139 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 14
      (PairLightPrepared4.rightCached.drop 139) (PairLightPrepared4.rightRows.drop 139) = true := right_prefix_001_part05_checked
  have h0125 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 28
      (PairLightPrepared4.rightCached.drop 125) (PairLightPrepared4.rightRows.drop 125) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 14 14
      (PairLightPrepared4.rightCached.drop 125) (PairLightPrepared4.rightRows.drop 125)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0139
  have h0111 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 42
      (PairLightPrepared4.rightCached.drop 111) (PairLightPrepared4.rightRows.drop 111) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 14 28
      (PairLightPrepared4.rightCached.drop 111) (PairLightPrepared4.rightRows.drop 111)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0125
  have h0097 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 56
      (PairLightPrepared4.rightCached.drop 97) (PairLightPrepared4.rightRows.drop 97) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 14 42
      (PairLightPrepared4.rightCached.drop 97) (PairLightPrepared4.rightRows.drop 97)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0111
  have h0084 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 69
      (PairLightPrepared4.rightCached.drop 84) (PairLightPrepared4.rightRows.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 13 56
      (PairLightPrepared4.rightCached.drop 84) (PairLightPrepared4.rightRows.drop 84)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0097
  have h0071 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 82
      (PairLightPrepared4.rightCached.drop 71) (PairLightPrepared4.rightRows.drop 71) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 13 69
      (PairLightPrepared4.rightCached.drop 71) (PairLightPrepared4.rightRows.drop 71)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0084
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0071

end D1Bound5.PairLightAdaptivePrepared4
end
