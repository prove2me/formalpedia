-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:27.222266+00:00
-- url     : https://prove2.me/submissions/f67405f5-9df4-4ed4-8161-8a8747abc8a0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 63
      leftCached001 leftRows001 = true := by
  have h0110 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 11
      (PairLightPrepared8.leftCached.drop 110) (PairLightPrepared8.leftRows.drop 110) = true := left_prefix_001_part05_checked
  have h0099 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 22
      (PairLightPrepared8.leftCached.drop 99) (PairLightPrepared8.leftRows.drop 99) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 11 11
      (PairLightPrepared8.leftCached.drop 99) (PairLightPrepared8.leftRows.drop 99)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0110
  have h0088 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 33
      (PairLightPrepared8.leftCached.drop 88) (PairLightPrepared8.leftRows.drop 88) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 11 22
      (PairLightPrepared8.leftCached.drop 88) (PairLightPrepared8.leftRows.drop 88)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0099
  have h0078 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 43
      (PairLightPrepared8.leftCached.drop 78) (PairLightPrepared8.leftRows.drop 78) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 10 33
      (PairLightPrepared8.leftCached.drop 78) (PairLightPrepared8.leftRows.drop 78)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0088
  have h0068 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 53
      (PairLightPrepared8.leftCached.drop 68) (PairLightPrepared8.leftRows.drop 68) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 10 43
      (PairLightPrepared8.leftCached.drop 68) (PairLightPrepared8.leftRows.drop 68)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0078
  have h0058 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 63
      (PairLightPrepared8.leftCached.drop 58) (PairLightPrepared8.leftRows.drop 58) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 10 53
      (PairLightPrepared8.leftCached.drop 58) (PairLightPrepared8.leftRows.drop 58)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0068
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0058

end D1Bound5.PairLightAdaptivePrepared8
end
