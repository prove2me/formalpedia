-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:07.289398+00:00
-- url     : https://prove2.me/submissions/adc0e1be-9ad3-4f25-ab51-8075ebcfffab

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 261; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 262
      rightCached000 rightRows000 = true := by
  have h131 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 131
      (rightCached000.drop 131) (rightRows000.drop 131) = true := right_prefix_000_part03_checked
  have h077 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 185
      (rightCached000.drop 77) (rightRows000.drop 77) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared18.sieve 54 131
      (rightCached000.drop 77) (rightRows000.drop 77)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h131
  have h035 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 227
      (rightCached000.drop 35) (rightRows000.drop 35) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared18.sieve 42 185
      (rightCached000.drop 35) (rightRows000.drop 35)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h077
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 262
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared18.sieve 35 227
      (rightCached000.drop 0) (rightRows000.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h035
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared18
end
