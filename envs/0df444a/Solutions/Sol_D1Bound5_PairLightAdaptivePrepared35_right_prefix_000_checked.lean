-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:26.642859+00:00
-- url     : https://prove2.me/submissions/e9290683-586c-47e0-b47f-375dacc6ec24

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 131; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 132
      rightCached000 rightRows000 = true := by
  have h131 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 1
      (rightCached000.drop 131) (rightRows000.drop 131) = true := right_prefix_000_part04_checked
  have h092 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 40
      (rightCached000.drop 92) (rightRows000.drop 92) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 39 1
      (rightCached000.drop 92) (rightRows000.drop 92)
    · exact right_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h131
  have h058 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 74
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 34 40
      (rightCached000.drop 58) (rightRows000.drop 58)
    · exact right_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h092
  have h028 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 104
      (rightCached000.drop 28) (rightRows000.drop 28) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 30 74
      (rightCached000.drop 28) (rightRows000.drop 28)
    · exact right_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h058
  have h000 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 132
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared35.sieve 28 104
      (rightCached000.drop 0) (rightRows000.drop 0)
    · exact right_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h028
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared35
end
