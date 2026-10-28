-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:22:05.752145+00:00
-- url     : https://prove2.me/submissions/27b60c9b-25fc-4658-a62d-257be8f91596

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData4_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 191
      rightCached004 rightRows004 = true := by
  have h0550 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 46
      (PairLightPrepared4.rightCached.drop 550) (PairLightPrepared4.rightRows.drop 550) = true := right_prefix_004_part03_checked
  have h0486 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 110
      (PairLightPrepared4.rightCached.drop 486) (PairLightPrepared4.rightRows.drop 486) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 64 46
      (PairLightPrepared4.rightCached.drop 486) (PairLightPrepared4.rightRows.drop 486)
    · exact right_prefix_004_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0550
  have h0441 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 155
      (PairLightPrepared4.rightCached.drop 441) (PairLightPrepared4.rightRows.drop 441) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 45 110
      (PairLightPrepared4.rightCached.drop 441) (PairLightPrepared4.rightRows.drop 441)
    · exact right_prefix_004_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0486
  have h0405 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 191
      (PairLightPrepared4.rightCached.drop 405) (PairLightPrepared4.rightRows.drop 405) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared4.sieve 36 155
      (PairLightPrepared4.rightCached.drop 405) (PairLightPrepared4.rightRows.drop 405)
    · exact right_prefix_004_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0441
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, rightCached003, rightRows003, rightCached004, rightRows004, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0405

end D1Bound5.PairLightAdaptivePrepared4
end
