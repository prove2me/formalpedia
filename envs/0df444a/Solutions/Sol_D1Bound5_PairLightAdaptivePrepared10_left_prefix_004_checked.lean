-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:31.298994+00:00
-- url     : https://prove2.me/submissions/74596ed0-630f-44dd-88e7-6221325ed11a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 191
      leftCached004 leftRows004 = true := by
  have h0550 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 46
      (PairLightPrepared10.leftCached.drop 550) (PairLightPrepared10.leftRows.drop 550) = true := left_prefix_004_part03_checked
  have h0486 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 110
      (PairLightPrepared10.leftCached.drop 486) (PairLightPrepared10.leftRows.drop 486) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 64 46
      (PairLightPrepared10.leftCached.drop 486) (PairLightPrepared10.leftRows.drop 486)
    · exact left_prefix_004_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0550
  have h0441 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 155
      (PairLightPrepared10.leftCached.drop 441) (PairLightPrepared10.leftRows.drop 441) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 45 110
      (PairLightPrepared10.leftCached.drop 441) (PairLightPrepared10.leftRows.drop 441)
    · exact left_prefix_004_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0486
  have h0405 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 191
      (PairLightPrepared10.leftCached.drop 405) (PairLightPrepared10.leftRows.drop 405) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared10.sieve 36 155
      (PairLightPrepared10.leftCached.drop 405) (PairLightPrepared10.leftRows.drop 405)
    · exact left_prefix_004_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0441
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, leftCached004, leftRows004, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0405

end D1Bound5.PairLightAdaptivePrepared10
end
