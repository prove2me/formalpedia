-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:24:25.435315+00:00
-- url     : https://prove2.me/submissions/3eb2c5c5-bfde-4345-9120-da0f8b240116

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_006_part14_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000

/-- Exact original head block with every complete later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 173
      rightCached006 rightRows006 = true := by
  have h168 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 5
      (rightCached006.drop 168) (rightRows006.drop 168) = true := right_prefix_006_part14_checked
  have h156 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 17
      (rightCached006.drop 156) (rightRows006.drop 156) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 5
      (rightCached006.drop 156) (rightRows006.drop 156)
    · exact right_prefix_006_part13_checked
    · simpa only [List.drop_drop] using h168
  have h144 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 29
      (rightCached006.drop 144) (rightRows006.drop 144) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 17
      (rightCached006.drop 144) (rightRows006.drop 144)
    · exact right_prefix_006_part12_checked
    · simpa only [List.drop_drop] using h156
  have h132 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 41
      (rightCached006.drop 132) (rightRows006.drop 132) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 29
      (rightCached006.drop 132) (rightRows006.drop 132)
    · exact right_prefix_006_part11_checked
    · simpa only [List.drop_drop] using h144
  have h120 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 53
      (rightCached006.drop 120) (rightRows006.drop 120) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 41
      (rightCached006.drop 120) (rightRows006.drop 120)
    · exact right_prefix_006_part10_checked
    · simpa only [List.drop_drop] using h132
  have h108 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 65
      (rightCached006.drop 108) (rightRows006.drop 108) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 53
      (rightCached006.drop 108) (rightRows006.drop 108)
    · exact right_prefix_006_part09_checked
    · simpa only [List.drop_drop] using h120
  have h096 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 77
      (rightCached006.drop 96) (rightRows006.drop 96) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 65
      (rightCached006.drop 96) (rightRows006.drop 96)
    · exact right_prefix_006_part08_checked
    · simpa only [List.drop_drop] using h108
  have h084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 89
      (rightCached006.drop 84) (rightRows006.drop 84) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 77
      (rightCached006.drop 84) (rightRows006.drop 84)
    · exact right_prefix_006_part07_checked
    · simpa only [List.drop_drop] using h096
  have h072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 101
      (rightCached006.drop 72) (rightRows006.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 89
      (rightCached006.drop 72) (rightRows006.drop 72)
    · exact right_prefix_006_part06_checked
    · simpa only [List.drop_drop] using h084
  have h060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 113
      (rightCached006.drop 60) (rightRows006.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 101
      (rightCached006.drop 60) (rightRows006.drop 60)
    · exact right_prefix_006_part05_checked
    · simpa only [List.drop_drop] using h072
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 125
      (rightCached006.drop 48) (rightRows006.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 113
      (rightCached006.drop 48) (rightRows006.drop 48)
    · exact right_prefix_006_part04_checked
    · simpa only [List.drop_drop] using h060
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 137
      (rightCached006.drop 36) (rightRows006.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 125
      (rightCached006.drop 36) (rightRows006.drop 36)
    · exact right_prefix_006_part03_checked
    · simpa only [List.drop_drop] using h048
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 149
      (rightCached006.drop 24) (rightRows006.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 137
      (rightCached006.drop 24) (rightRows006.drop 24)
    · exact right_prefix_006_part02_checked
    · simpa only [List.drop_drop] using h036
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 161
      (rightCached006.drop 12) (rightRows006.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 149
      (rightCached006.drop 12) (rightRows006.drop 12)
    · exact right_prefix_006_part01_checked
    · simpa only [List.drop_drop] using h024
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 173
      (rightCached006.drop 0) (rightRows006.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 12 161
      (rightCached006.drop 0) (rightRows006.drop 0)
    · exact right_prefix_006_part00_checked
    · simpa only [List.drop_drop] using h012
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared26
end
