-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:28:29.380369+00:00
-- url     : https://prove2.me/submissions/60420d08-090c-4927-b652-6cd405ea1ca7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData6_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_005_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 189
      leftCached005 leftRows005 = true := by
  have h0618 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 40
      (PairLightPrepared6.leftCached.drop 618) (PairLightPrepared6.leftRows.drop 618) = true := left_prefix_005_part03_checked
  have h0552 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 106
      (PairLightPrepared6.leftCached.drop 552) (PairLightPrepared6.leftRows.drop 552) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 66 40
      (PairLightPrepared6.leftCached.drop 552) (PairLightPrepared6.leftRows.drop 552)
    · exact left_prefix_005_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0618
  have h0506 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 152
      (PairLightPrepared6.leftCached.drop 506) (PairLightPrepared6.leftRows.drop 506) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 46 106
      (PairLightPrepared6.leftCached.drop 506) (PairLightPrepared6.leftRows.drop 506)
    · exact left_prefix_005_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0552
  have h0469 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 189
      (PairLightPrepared6.leftCached.drop 469) (PairLightPrepared6.leftRows.drop 469) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared6.sieve 37 152
      (PairLightPrepared6.leftCached.drop 469) (PairLightPrepared6.leftRows.drop 469)
    · exact left_prefix_005_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0506
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, leftCached004, leftRows004, leftCached005, leftRows005, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0469

end D1Bound5.PairLightAdaptivePrepared6
end
