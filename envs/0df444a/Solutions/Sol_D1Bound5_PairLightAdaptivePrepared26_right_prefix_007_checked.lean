-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:37.132963+00:00
-- url     : https://prove2.me/submissions/123c5933-026c-468e-991c-0f475c07ae3d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_007_part12_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000

/-- Exact original head block with every complete later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 145
      rightCached007 rightRows007 = true := by
  have h144 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (rightCached007.drop 144) (rightRows007.drop 144) = true := right_prefix_007_part12_checked
  have h132 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 13
      (rightCached007.drop 132) (rightRows007.drop 132) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 1
      (rightCached007.drop 132) (rightRows007.drop 132)
    · exact right_prefix_007_part11_checked
    · simpa only [List.drop_drop] using h144
  have h120 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 25
      (rightCached007.drop 120) (rightRows007.drop 120) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 13
      (rightCached007.drop 120) (rightRows007.drop 120)
    · exact right_prefix_007_part10_checked
    · simpa only [List.drop_drop] using h132
  have h108 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 37
      (rightCached007.drop 108) (rightRows007.drop 108) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 25
      (rightCached007.drop 108) (rightRows007.drop 108)
    · exact right_prefix_007_part09_checked
    · simpa only [List.drop_drop] using h120
  have h096 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 49
      (rightCached007.drop 96) (rightRows007.drop 96) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 37
      (rightCached007.drop 96) (rightRows007.drop 96)
    · exact right_prefix_007_part08_checked
    · simpa only [List.drop_drop] using h108
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 61
      (rightCached007.drop 84) (rightRows007.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 49
      (rightCached007.drop 84) (rightRows007.drop 84)
    · exact right_prefix_007_part07_checked
    · simpa only [List.drop_drop] using h096
  have h072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 73
      (rightCached007.drop 72) (rightRows007.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 61
      (rightCached007.drop 72) (rightRows007.drop 72)
    · exact right_prefix_007_part06_checked
    · simpa only [List.drop_drop] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 85
      (rightCached007.drop 60) (rightRows007.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 73
      (rightCached007.drop 60) (rightRows007.drop 60)
    · exact right_prefix_007_part05_checked
    · simpa only [List.drop_drop] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 97
      (rightCached007.drop 48) (rightRows007.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 85
      (rightCached007.drop 48) (rightRows007.drop 48)
    · exact right_prefix_007_part04_checked
    · simpa only [List.drop_drop] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 109
      (rightCached007.drop 36) (rightRows007.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 97
      (rightCached007.drop 36) (rightRows007.drop 36)
    · exact right_prefix_007_part03_checked
    · simpa only [List.drop_drop] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 121
      (rightCached007.drop 24) (rightRows007.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 109
      (rightCached007.drop 24) (rightRows007.drop 24)
    · exact right_prefix_007_part02_checked
    · simpa only [List.drop_drop] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 133
      (rightCached007.drop 12) (rightRows007.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 121
      (rightCached007.drop 12) (rightRows007.drop 12)
    · exact right_prefix_007_part01_checked
    · simpa only [List.drop_drop] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 145
      (rightCached007.drop 0) (rightRows007.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 133
      (rightCached007.drop 0) (rightRows007.drop 0)
    · exact right_prefix_007_part00_checked
    · simpa only [List.drop_drop] using h012
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared26
end
