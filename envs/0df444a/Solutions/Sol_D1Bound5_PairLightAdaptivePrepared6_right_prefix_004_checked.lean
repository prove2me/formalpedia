-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:30.689927+00:00
-- url     : https://prove2.me/submissions/17aaf13d-3732-46c2-8302-df2c4871d7fd

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 155
      rightCached004 rightRows004 = true := by
  have h0471 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 5
      (PairLightPrepared6.rightCached.drop 471) (PairLightPrepared6.rightRows.drop 471) = true := right_prefix_004_part06_checked
  have h0439 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 37
      (PairLightPrepared6.rightCached.drop 439) (PairLightPrepared6.rightRows.drop 439) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 32 5
      (PairLightPrepared6.rightCached.drop 439) (PairLightPrepared6.rightRows.drop 439)
    · exact right_prefix_004_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0471
  have h0411 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 65
      (PairLightPrepared6.rightCached.drop 411) (PairLightPrepared6.rightRows.drop 411) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 28 37
      (PairLightPrepared6.rightCached.drop 411) (PairLightPrepared6.rightRows.drop 411)
    · exact right_prefix_004_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0439
  have h0386 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 90
      (PairLightPrepared6.rightCached.drop 386) (PairLightPrepared6.rightRows.drop 386) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 25 65
      (PairLightPrepared6.rightCached.drop 386) (PairLightPrepared6.rightRows.drop 386)
    · exact right_prefix_004_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0411
  have h0363 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 113
      (PairLightPrepared6.rightCached.drop 363) (PairLightPrepared6.rightRows.drop 363) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 23 90
      (PairLightPrepared6.rightCached.drop 363) (PairLightPrepared6.rightRows.drop 363)
    · exact right_prefix_004_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0386
  have h0341 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 135
      (PairLightPrepared6.rightCached.drop 341) (PairLightPrepared6.rightRows.drop 341) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 22 113
      (PairLightPrepared6.rightCached.drop 341) (PairLightPrepared6.rightRows.drop 341)
    · exact right_prefix_004_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0363
  have h0321 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 155
      (PairLightPrepared6.rightCached.drop 321) (PairLightPrepared6.rightRows.drop 321) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 20 135
      (PairLightPrepared6.rightCached.drop 321) (PairLightPrepared6.rightRows.drop 321)
    · exact right_prefix_004_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0341
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, rightCached003, rightRows003, rightCached004, rightRows004, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0321

end D1Bound5.PairLightAdaptivePrepared6
end
