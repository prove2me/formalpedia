-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:30:51.30596+00:00
-- url     : https://prove2.me/submissions/1260c137-aade-4ee0-9fda-43977deda640

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 71
      leftCached001 leftRows001 = true := by
  have h0122 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.leftCached.drop 122) (PairLightPrepared6.leftRows.drop 122) = true := left_prefix_001_part05_checked
  have h0110 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 24
      (PairLightPrepared6.leftCached.drop 110) (PairLightPrepared6.leftRows.drop 110) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 12
      (PairLightPrepared6.leftCached.drop 110) (PairLightPrepared6.leftRows.drop 110)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0122
  have h0098 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 36
      (PairLightPrepared6.leftCached.drop 98) (PairLightPrepared6.leftRows.drop 98) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 24
      (PairLightPrepared6.leftCached.drop 98) (PairLightPrepared6.leftRows.drop 98)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0110
  have h0086 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 48
      (PairLightPrepared6.leftCached.drop 86) (PairLightPrepared6.leftRows.drop 86) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 36
      (PairLightPrepared6.leftCached.drop 86) (PairLightPrepared6.leftRows.drop 86)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0098
  have h0074 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 60
      (PairLightPrepared6.leftCached.drop 74) (PairLightPrepared6.leftRows.drop 74) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 12 48
      (PairLightPrepared6.leftCached.drop 74) (PairLightPrepared6.leftRows.drop 74)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0086
  have h0063 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 71
      (PairLightPrepared6.leftCached.drop 63) (PairLightPrepared6.leftRows.drop 63) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 11 60
      (PairLightPrepared6.leftCached.drop 63) (PairLightPrepared6.leftRows.drop 63)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0074
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0063

end D1Bound5.PairLightAdaptivePrepared6
end
