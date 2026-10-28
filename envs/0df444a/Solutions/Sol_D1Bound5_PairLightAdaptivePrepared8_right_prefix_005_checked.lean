-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:29:35.708011+00:00
-- url     : https://prove2.me/submissions/05ed3246-0d46-4442-8d2e-0a2cfb8a6ff0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_prefix_005_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 149
      rightCached005 rightRows005 = true := by
  have h0521 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 3
      (PairLightPrepared8.rightCached.drop 521) (PairLightPrepared8.rightRows.drop 521) = true := right_prefix_005_part06_checked
  have h0491 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 33
      (PairLightPrepared8.rightCached.drop 491) (PairLightPrepared8.rightRows.drop 491) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 30 3
      (PairLightPrepared8.rightCached.drop 491) (PairLightPrepared8.rightRows.drop 491)
    · exact right_prefix_005_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0521
  have h0464 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 60
      (PairLightPrepared8.rightCached.drop 464) (PairLightPrepared8.rightRows.drop 464) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 27 33
      (PairLightPrepared8.rightCached.drop 464) (PairLightPrepared8.rightRows.drop 464)
    · exact right_prefix_005_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0491
  have h0439 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 85
      (PairLightPrepared8.rightCached.drop 439) (PairLightPrepared8.rightRows.drop 439) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 25 60
      (PairLightPrepared8.rightCached.drop 439) (PairLightPrepared8.rightRows.drop 439)
    · exact right_prefix_005_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0464
  have h0416 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 108
      (PairLightPrepared8.rightCached.drop 416) (PairLightPrepared8.rightRows.drop 416) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 23 85
      (PairLightPrepared8.rightCached.drop 416) (PairLightPrepared8.rightRows.drop 416)
    · exact right_prefix_005_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0439
  have h0395 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 129
      (PairLightPrepared8.rightCached.drop 395) (PairLightPrepared8.rightRows.drop 395) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 21 108
      (PairLightPrepared8.rightCached.drop 395) (PairLightPrepared8.rightRows.drop 395)
    · exact right_prefix_005_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0416
  have h0375 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 149
      (PairLightPrepared8.rightCached.drop 375) (PairLightPrepared8.rightRows.drop 375) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 20 129
      (PairLightPrepared8.rightCached.drop 375) (PairLightPrepared8.rightRows.drop 375)
    · exact right_prefix_005_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0395
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, rightCached003, rightRows003, rightCached004, rightRows004, rightCached005, rightRows005, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0375

end D1Bound5.PairLightAdaptivePrepared8
end
