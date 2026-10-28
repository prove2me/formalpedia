-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:30.948962+00:00
-- url     : https://prove2.me/submissions/45f72526-407a-44c5-9b79-1d26bcd17214

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part07_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000

/-- Exact original head block with every complete later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 85
      rightCached004 rightRows004 = true := by
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (rightCached004.drop 84) (rightRows004.drop 84) = true := right_prefix_004_part07_checked
  have h072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 13
      (rightCached004.drop 72) (rightRows004.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 1
      (rightCached004.drop 72) (rightRows004.drop 72)
    · exact right_prefix_004_part06_checked
    · simpa only [List.drop_drop] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 25
      (rightCached004.drop 60) (rightRows004.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 13
      (rightCached004.drop 60) (rightRows004.drop 60)
    · exact right_prefix_004_part05_checked
    · simpa only [List.drop_drop] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 37
      (rightCached004.drop 48) (rightRows004.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 25
      (rightCached004.drop 48) (rightRows004.drop 48)
    · exact right_prefix_004_part04_checked
    · simpa only [List.drop_drop] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 49
      (rightCached004.drop 36) (rightRows004.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 37
      (rightCached004.drop 36) (rightRows004.drop 36)
    · exact right_prefix_004_part03_checked
    · simpa only [List.drop_drop] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 61
      (rightCached004.drop 24) (rightRows004.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 49
      (rightCached004.drop 24) (rightRows004.drop 24)
    · exact right_prefix_004_part02_checked
    · simpa only [List.drop_drop] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 73
      (rightCached004.drop 12) (rightRows004.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 61
      (rightCached004.drop 12) (rightRows004.drop 12)
    · exact right_prefix_004_part01_checked
    · simpa only [List.drop_drop] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 85
      (rightCached004.drop 0) (rightRows004.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 73
      (rightCached004.drop 0) (rightRows004.drop 0)
    · exact right_prefix_004_part00_checked
    · simpa only [List.drop_drop] using h012
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared26
end
