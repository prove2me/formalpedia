-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_006_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:22.980758+00:00
-- url     : https://prove2.me/submissions/3cbb3989-bd30-42ca-8a26-bc539091357c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData8_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_prefix_006_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 189
      leftCached006 leftRows006 = true := by
  have h0676 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 40
      (PairLightPrepared8.leftCached.drop 676) (PairLightPrepared8.leftRows.drop 676) = true := left_prefix_006_part03_checked
  have h0610 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 106
      (PairLightPrepared8.leftCached.drop 610) (PairLightPrepared8.leftRows.drop 610) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 66 40
      (PairLightPrepared8.leftCached.drop 610) (PairLightPrepared8.leftRows.drop 610)
    · exact left_prefix_006_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0676
  have h0564 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 152
      (PairLightPrepared8.leftCached.drop 564) (PairLightPrepared8.leftRows.drop 564) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 46 106
      (PairLightPrepared8.leftCached.drop 564) (PairLightPrepared8.leftRows.drop 564)
    · exact left_prefix_006_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0610
  have h0527 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 189
      (PairLightPrepared8.leftCached.drop 527) (PairLightPrepared8.leftRows.drop 527) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared8.sieve 37 152
      (PairLightPrepared8.leftCached.drop 527) (PairLightPrepared8.leftRows.drop 527)
    · exact left_prefix_006_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0564
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, leftCached003, leftRows003, leftCached004, leftRows004, leftCached005, leftRows005, leftCached006, leftRows006, List.drop_drop, Nat.reduceAdd, List.drop_zero] using h0527

end D1Bound5.PairLightAdaptivePrepared8
end
