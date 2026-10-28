-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:28:27.574657+00:00
-- url     : https://prove2.me/submissions/07d4e572-f62f-4619-9340-1fcd025ff489

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 63
      leftCached000 leftRows000 = true := by
  have h0052 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.leftCached.drop 52) (PairLightPrepared6.leftRows.drop 52) = true := left_prefix_000_part05_checked
  have h0041 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 22
      (PairLightPrepared6.leftCached.drop 41) (PairLightPrepared6.leftRows.drop 41) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 11
      (PairLightPrepared6.leftCached.drop 41) (PairLightPrepared6.leftRows.drop 41)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0052
  have h0030 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 33
      (PairLightPrepared6.leftCached.drop 30) (PairLightPrepared6.leftRows.drop 30) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 22
      (PairLightPrepared6.leftCached.drop 30) (PairLightPrepared6.leftRows.drop 30)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0041
  have h0020 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 43
      (PairLightPrepared6.leftCached.drop 20) (PairLightPrepared6.leftRows.drop 20) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 10 33
      (PairLightPrepared6.leftCached.drop 20) (PairLightPrepared6.leftRows.drop 20)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0030
  have h0010 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 53
      (PairLightPrepared6.leftCached.drop 10) (PairLightPrepared6.leftRows.drop 10) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 10 43
      (PairLightPrepared6.leftCached.drop 10) (PairLightPrepared6.leftRows.drop 10)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0020
  have h0000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 63
      (PairLightPrepared6.leftCached.drop 0) (PairLightPrepared6.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 10 53
      (PairLightPrepared6.leftCached.drop 0) (PairLightPrepared6.leftRows.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0010
  simpa only [leftCached000, leftRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0000

end D1Bound5.PairLightAdaptivePrepared6
end
