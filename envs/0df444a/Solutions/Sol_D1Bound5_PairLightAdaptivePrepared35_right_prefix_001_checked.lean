-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:22:09.639975+00:00
-- url     : https://prove2.me/submissions/65643895-3d5f-478b-9690-b45c2a85e3ef

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 132 through 367; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 236
      rightCached001 rightRows001 = true := by
  have h110 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 126
      (rightCached001.drop 110) (rightRows001.drop 110) = true := right_prefix_001_part02_checked
  have h047 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 189
      (rightCached001.drop 47) (rightRows001.drop 47) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 63 126
      (rightCached001.drop 47) (rightRows001.drop 47)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop] using h110
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 236
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 47 189
      (rightCached001.drop 0) (rightRows001.drop 0)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop] using h047
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared35
end
