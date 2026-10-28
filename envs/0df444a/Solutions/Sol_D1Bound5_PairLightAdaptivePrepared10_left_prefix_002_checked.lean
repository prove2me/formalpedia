-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:15.799834+00:00
-- url     : https://prove2.me/submissions/63b377a5-558a-44b1-b11f-58a4a6d797a5

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 102
      leftCached002 leftRows002 = true := by
  have h0236 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 19
      (PairLightPrepared10.leftCached.drop 236) (PairLightPrepared10.leftRows.drop 236) = true := left_prefix_002_part05_checked
  have h0218 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 37
      (PairLightPrepared10.leftCached.drop 218) (PairLightPrepared10.leftRows.drop 218) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 18 19
      (PairLightPrepared10.leftCached.drop 218) (PairLightPrepared10.leftRows.drop 218)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0236
  have h0201 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 54
      (PairLightPrepared10.leftCached.drop 201) (PairLightPrepared10.leftRows.drop 201) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 17 37
      (PairLightPrepared10.leftCached.drop 201) (PairLightPrepared10.leftRows.drop 201)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0218
  have h0184 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 71
      (PairLightPrepared10.leftCached.drop 184) (PairLightPrepared10.leftRows.drop 184) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 17 54
      (PairLightPrepared10.leftCached.drop 184) (PairLightPrepared10.leftRows.drop 184)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0201
  have h0168 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 87
      (PairLightPrepared10.leftCached.drop 168) (PairLightPrepared10.leftRows.drop 168) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 16 71
      (PairLightPrepared10.leftCached.drop 168) (PairLightPrepared10.leftRows.drop 168)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0184
  have h0153 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 102
      (PairLightPrepared10.leftCached.drop 153) (PairLightPrepared10.leftRows.drop 153) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 15 87
      (PairLightPrepared10.leftCached.drop 153) (PairLightPrepared10.leftRows.drop 153)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0168
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0153

end D1Bound5.PairLightAdaptivePrepared10
end
