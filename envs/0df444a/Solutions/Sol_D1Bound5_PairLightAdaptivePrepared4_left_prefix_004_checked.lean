-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:29.334885+00:00
-- url     : https://prove2.me/submissions/8dc4366b-3b7e-4006-8a4b-ffab4a8a1246

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 191
      leftCached004 leftRows004 = true := by
  have h0550 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 46
      (PairLightPrepared4.leftCached.drop 550) (PairLightPrepared4.leftRows.drop 550) = true := left_prefix_004_part03_checked
  have h0486 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 110
      (PairLightPrepared4.leftCached.drop 486) (PairLightPrepared4.leftRows.drop 486) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 64 46
      (PairLightPrepared4.leftCached.drop 486) (PairLightPrepared4.leftRows.drop 486)
    · exact left_prefix_004_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0550
  have h0441 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 155
      (PairLightPrepared4.leftCached.drop 441) (PairLightPrepared4.leftRows.drop 441) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 45 110
      (PairLightPrepared4.leftCached.drop 441) (PairLightPrepared4.leftRows.drop 441)
    · exact left_prefix_004_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0486
  have h0405 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 191
      (PairLightPrepared4.leftCached.drop 405) (PairLightPrepared4.leftRows.drop 405) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 36 155
      (PairLightPrepared4.leftCached.drop 405) (PairLightPrepared4.leftRows.drop 405)
    · exact left_prefix_004_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0441
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, leftCached004, leftRows004, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0405

end D1Bound5.PairLightAdaptivePrepared4
end
