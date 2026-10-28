-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:35.461867+00:00
-- url     : https://prove2.me/submissions/5215ed18-73be-4c4c-934b-8fe31d614e47

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 138 through 358; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 221
      leftCached001 leftRows001 = true := by
  have h127 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 94
      (leftCached001.drop 127) (leftRows001.drop 127) = true := left_prefix_001_part02_checked
  have h051 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 170
      (leftCached001.drop 51) (leftRows001.drop 51) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared12.sieve 76 94
      (leftCached001.drop 51) (leftRows001.drop 51)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop] using h127
  have h000 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 221
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared12.sieve 51 170
      (leftCached001.drop 0) (leftRows001.drop 0)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop] using h051
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared12
end
