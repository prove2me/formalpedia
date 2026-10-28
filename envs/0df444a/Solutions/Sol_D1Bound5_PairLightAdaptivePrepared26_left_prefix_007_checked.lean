-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:26:35.264445+00:00
-- url     : https://prove2.me/submissions/6b9ddfc9-2e65-42cb-bb07-e77b428401c2

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_007_part12_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000

/-- Exact original head block with every complete later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 145
      leftCached007 leftRows007 = true := by
  have h144 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (leftCached007.drop 144) (leftRows007.drop 144) = true := left_prefix_007_part12_checked
  have h132 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 13
      (leftCached007.drop 132) (leftRows007.drop 132) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 1
      (leftCached007.drop 132) (leftRows007.drop 132)
    · exact left_prefix_007_part11_checked
    · simpa only [List.drop_drop] using h144
  have h120 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 25
      (leftCached007.drop 120) (leftRows007.drop 120) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 13
      (leftCached007.drop 120) (leftRows007.drop 120)
    · exact left_prefix_007_part10_checked
    · simpa only [List.drop_drop] using h132
  have h108 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 37
      (leftCached007.drop 108) (leftRows007.drop 108) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 25
      (leftCached007.drop 108) (leftRows007.drop 108)
    · exact left_prefix_007_part09_checked
    · simpa only [List.drop_drop] using h120
  have h096 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 49
      (leftCached007.drop 96) (leftRows007.drop 96) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 37
      (leftCached007.drop 96) (leftRows007.drop 96)
    · exact left_prefix_007_part08_checked
    · simpa only [List.drop_drop] using h108
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 61
      (leftCached007.drop 84) (leftRows007.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 49
      (leftCached007.drop 84) (leftRows007.drop 84)
    · exact left_prefix_007_part07_checked
    · simpa only [List.drop_drop] using h096
  have h072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 73
      (leftCached007.drop 72) (leftRows007.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 61
      (leftCached007.drop 72) (leftRows007.drop 72)
    · exact left_prefix_007_part06_checked
    · simpa only [List.drop_drop] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 85
      (leftCached007.drop 60) (leftRows007.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 73
      (leftCached007.drop 60) (leftRows007.drop 60)
    · exact left_prefix_007_part05_checked
    · simpa only [List.drop_drop] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 97
      (leftCached007.drop 48) (leftRows007.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 85
      (leftCached007.drop 48) (leftRows007.drop 48)
    · exact left_prefix_007_part04_checked
    · simpa only [List.drop_drop] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 109
      (leftCached007.drop 36) (leftRows007.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 97
      (leftCached007.drop 36) (leftRows007.drop 36)
    · exact left_prefix_007_part03_checked
    · simpa only [List.drop_drop] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 121
      (leftCached007.drop 24) (leftRows007.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 109
      (leftCached007.drop 24) (leftRows007.drop 24)
    · exact left_prefix_007_part02_checked
    · simpa only [List.drop_drop] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 133
      (leftCached007.drop 12) (leftRows007.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 121
      (leftCached007.drop 12) (leftRows007.drop 12)
    · exact left_prefix_007_part01_checked
    · simpa only [List.drop_drop] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 145
      (leftCached007.drop 0) (leftRows007.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 133
      (leftCached007.drop 0) (leftRows007.drop 0)
    · exact left_prefix_007_part00_checked
    · simpa only [List.drop_drop] using h012
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared26
end
