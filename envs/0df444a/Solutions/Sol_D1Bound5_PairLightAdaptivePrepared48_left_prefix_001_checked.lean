-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:31:02.46541+00:00
-- url     : https://prove2.me/submissions/440cd907-516b-44b4-9654-1493492007e8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 137 through 359; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 223
      leftCached001 leftRows001 = true := by
  have h123 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 100
      (leftCached001.drop 123) (leftRows001.drop 123) = true := left_prefix_001_part02_checked
  have h050 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 173
      (leftCached001.drop 50) (leftRows001.drop 50) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 8 PairLightPrepared48.sieve 73 100
      (leftCached001.drop 50) (leftRows001.drop 50)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop] using h123
  have h000 : pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 223
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 8 PairLightPrepared48.sieve 50 173
      (leftCached001.drop 0) (leftRows001.drop 0)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop] using h050
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared48
end
