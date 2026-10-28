-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:27.467986+00:00
-- url     : https://prove2.me/submissions/43f4caaf-1667-4e5d-84b1-c43df03280b2

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 132 through 368; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 237
      leftCached001 leftRows001 = true := by
  have h108 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 129
      (leftCached001.drop 108) (leftRows001.drop 108) = true := left_prefix_001_part02_checked
  have h046 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 191
      (leftCached001.drop 46) (leftRows001.drop 46) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 62 129
      (leftCached001.drop 46) (leftRows001.drop 46)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop] using h108
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 237
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 46 191
      (leftCached001.drop 0) (leftRows001.drop 0)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop] using h046
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared35
end
