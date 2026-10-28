-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:33.100327+00:00
-- url     : https://prove2.me/submissions/c5da50ab-12d6-46e0-8dc4-c76e7fd901cb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_002_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 158
      (PairLightPrepared7.rightCached.drop 272) (PairLightPrepared7.rightRows.drop 272) = true := by
  have h416 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 14
      (PairLightPrepared7.rightCached.drop 416) (PairLightPrepared7.rightRows.drop 416) = true := right_prefix_002_part06_checked
  have h392 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 38
      (PairLightPrepared7.rightCached.drop 392) (PairLightPrepared7.rightRows.drop 392) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 14
      (PairLightPrepared7.rightCached.drop 392) (PairLightPrepared7.rightRows.drop 392)
    · exact right_prefix_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h416
  have h368 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 62
      (PairLightPrepared7.rightCached.drop 368) (PairLightPrepared7.rightRows.drop 368) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 38
      (PairLightPrepared7.rightCached.drop 368) (PairLightPrepared7.rightRows.drop 368)
    · exact right_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h392
  have h344 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 86
      (PairLightPrepared7.rightCached.drop 344) (PairLightPrepared7.rightRows.drop 344) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 62
      (PairLightPrepared7.rightCached.drop 344) (PairLightPrepared7.rightRows.drop 344)
    · exact right_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h368
  have h320 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 110
      (PairLightPrepared7.rightCached.drop 320) (PairLightPrepared7.rightRows.drop 320) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 86
      (PairLightPrepared7.rightCached.drop 320) (PairLightPrepared7.rightRows.drop 320)
    · exact right_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h344
  have h296 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 134
      (PairLightPrepared7.rightCached.drop 296) (PairLightPrepared7.rightRows.drop 296) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 110
      (PairLightPrepared7.rightCached.drop 296) (PairLightPrepared7.rightRows.drop 296)
    · exact right_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h320
  have h272 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 158
      (PairLightPrepared7.rightCached.drop 272) (PairLightPrepared7.rightRows.drop 272) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 134
      (PairLightPrepared7.rightCached.drop 272) (PairLightPrepared7.rightRows.drop 272)
    · exact right_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h296
  exact h272
end D1Bound5.PairLightAdaptivePrepared7
end
