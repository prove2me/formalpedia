-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:19:17.464518+00:00
-- url     : https://prove2.me/submissions/cce84290-4cc2-4d24-a8ad-263aa70d10d1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 71
      leftCached002 leftRows002 = true := by
  have h0180 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 180) (PairLightPrepared8.leftRows.drop 180) = true := left_prefix_002_part05_checked
  have h0168 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 24
      (PairLightPrepared8.leftCached.drop 168) (PairLightPrepared8.leftRows.drop 168) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 12
      (PairLightPrepared8.leftCached.drop 168) (PairLightPrepared8.leftRows.drop 168)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0180
  have h0156 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 36
      (PairLightPrepared8.leftCached.drop 156) (PairLightPrepared8.leftRows.drop 156) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 24
      (PairLightPrepared8.leftCached.drop 156) (PairLightPrepared8.leftRows.drop 156)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0168
  have h0144 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 48
      (PairLightPrepared8.leftCached.drop 144) (PairLightPrepared8.leftRows.drop 144) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 36
      (PairLightPrepared8.leftCached.drop 144) (PairLightPrepared8.leftRows.drop 144)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0156
  have h0132 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 60
      (PairLightPrepared8.leftCached.drop 132) (PairLightPrepared8.leftRows.drop 132) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 12 48
      (PairLightPrepared8.leftCached.drop 132) (PairLightPrepared8.leftRows.drop 132)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0144
  have h0121 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 71
      (PairLightPrepared8.leftCached.drop 121) (PairLightPrepared8.leftRows.drop 121) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 11 60
      (PairLightPrepared8.leftCached.drop 121) (PairLightPrepared8.leftRows.drop 121)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0132
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0121

end D1Bound5.PairLightAdaptivePrepared8
end
