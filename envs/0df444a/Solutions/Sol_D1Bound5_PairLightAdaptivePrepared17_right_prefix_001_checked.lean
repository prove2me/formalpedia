-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:30:50.403145+00:00
-- url     : https://prove2.me/submissions/dd2bbb32-348c-4b49-a731-9dc2db05406a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 138 through 357; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 220
      rightCached001 rightRows001 = true := by
  have h127 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 93
      (rightCached001.drop 127) (rightRows001.drop 127) = true := right_prefix_001_part02_checked
  have h051 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 169
      (rightCached001.drop 51) (rightRows001.drop 51) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared17.sieve 76 93
      (rightCached001.drop 51) (rightRows001.drop 51)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop] using h127
  have h000 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 220
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared17.sieve 51 169
      (rightCached001.drop 0) (rightRows001.drop 0)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop] using h051
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared17
end
