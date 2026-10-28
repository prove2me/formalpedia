-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:31:58.470197+00:00
-- url     : https://prove2.me/submissions/f55e7cb2-341c-4443-bce5-db9e6b4b7e37

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 102
      leftCached002 leftRows002 = true := by
  have h0236 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 19
      (PairLightPrepared4.leftCached.drop 236) (PairLightPrepared4.leftRows.drop 236) = true := left_prefix_002_part05_checked
  have h0218 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 37
      (PairLightPrepared4.leftCached.drop 218) (PairLightPrepared4.leftRows.drop 218) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 18 19
      (PairLightPrepared4.leftCached.drop 218) (PairLightPrepared4.leftRows.drop 218)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0236
  have h0201 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 54
      (PairLightPrepared4.leftCached.drop 201) (PairLightPrepared4.leftRows.drop 201) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 17 37
      (PairLightPrepared4.leftCached.drop 201) (PairLightPrepared4.leftRows.drop 201)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0218
  have h0184 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 71
      (PairLightPrepared4.leftCached.drop 184) (PairLightPrepared4.leftRows.drop 184) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 17 54
      (PairLightPrepared4.leftCached.drop 184) (PairLightPrepared4.leftRows.drop 184)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0201
  have h0168 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 87
      (PairLightPrepared4.leftCached.drop 168) (PairLightPrepared4.leftRows.drop 168) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 16 71
      (PairLightPrepared4.leftCached.drop 168) (PairLightPrepared4.leftRows.drop 168)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0184
  have h0153 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 102
      (PairLightPrepared4.leftCached.drop 153) (PairLightPrepared4.leftRows.drop 153) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 15 87
      (PairLightPrepared4.leftCached.drop 153) (PairLightPrepared4.leftRows.drop 153)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0168
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0153

end D1Bound5.PairLightAdaptivePrepared4
end
