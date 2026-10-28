-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:26:36.113683+00:00
-- url     : https://prove2.me/submissions/bf6fb4e4-b693-4f36-9e92-71f2663fb733

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 254
      leftCached001 leftRows001 = true := by
  have h149 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 105
      (leftCached001.drop 149) (leftRows001.drop 149) = true := left_prefix_001_part03_checked
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 170
      (leftCached001.drop 84) (leftRows001.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 65 105
      (leftCached001.drop 84) (leftRows001.drop 84)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h149
  have h038 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 216
      (leftCached001.drop 38) (leftRows001.drop 38) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 46 170
      (leftCached001.drop 38) (leftRows001.drop 38)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h084
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 254
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared29.sieve 38 216
      (leftCached001.drop 0) (leftRows001.drop 0)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h038
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared29
end
