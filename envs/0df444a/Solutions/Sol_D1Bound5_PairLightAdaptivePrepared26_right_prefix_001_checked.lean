-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:21.802731+00:00
-- url     : https://prove2.me/submissions/17f0ead4-5497-4fdd-8f0b-4749fac7f180

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part18_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_001_part19_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000

/-- Exact original head block; every head retains its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 59
      rightCached001 rightRows001 = true := by
  have h057 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 2
      (rightCached001.drop 57) (rightRows001.drop 57) = true := right_prefix_001_part19_checked
  have h054 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 5
      (rightCached001.drop 54) (rightRows001.drop 54) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 2
      (rightCached001.drop 54) (rightRows001.drop 54)
    · exact right_prefix_001_part18_checked
    · simpa only [List.drop_drop] using h057
  have h051 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 8
      (rightCached001.drop 51) (rightRows001.drop 51) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 5
      (rightCached001.drop 51) (rightRows001.drop 51)
    · exact right_prefix_001_part17_checked
    · simpa only [List.drop_drop] using h054
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 11
      (rightCached001.drop 48) (rightRows001.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 8
      (rightCached001.drop 48) (rightRows001.drop 48)
    · exact right_prefix_001_part16_checked
    · simpa only [List.drop_drop] using h051
  have h045 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 14
      (rightCached001.drop 45) (rightRows001.drop 45) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 11
      (rightCached001.drop 45) (rightRows001.drop 45)
    · exact right_prefix_001_part15_checked
    · simpa only [List.drop_drop] using h048
  have h042 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 17
      (rightCached001.drop 42) (rightRows001.drop 42) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 14
      (rightCached001.drop 42) (rightRows001.drop 42)
    · exact right_prefix_001_part14_checked
    · simpa only [List.drop_drop] using h045
  have h039 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 20
      (rightCached001.drop 39) (rightRows001.drop 39) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 17
      (rightCached001.drop 39) (rightRows001.drop 39)
    · exact right_prefix_001_part13_checked
    · simpa only [List.drop_drop] using h042
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 23
      (rightCached001.drop 36) (rightRows001.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 20
      (rightCached001.drop 36) (rightRows001.drop 36)
    · exact right_prefix_001_part12_checked
    · simpa only [List.drop_drop] using h039
  have h033 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 26
      (rightCached001.drop 33) (rightRows001.drop 33) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 23
      (rightCached001.drop 33) (rightRows001.drop 33)
    · exact right_prefix_001_part11_checked
    · simpa only [List.drop_drop] using h036
  have h030 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 29
      (rightCached001.drop 30) (rightRows001.drop 30) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 26
      (rightCached001.drop 30) (rightRows001.drop 30)
    · exact right_prefix_001_part10_checked
    · simpa only [List.drop_drop] using h033
  have h027 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 32
      (rightCached001.drop 27) (rightRows001.drop 27) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 29
      (rightCached001.drop 27) (rightRows001.drop 27)
    · exact right_prefix_001_part09_checked
    · simpa only [List.drop_drop] using h030
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 35
      (rightCached001.drop 24) (rightRows001.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 32
      (rightCached001.drop 24) (rightRows001.drop 24)
    · exact right_prefix_001_part08_checked
    · simpa only [List.drop_drop] using h027
  have h021 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 38
      (rightCached001.drop 21) (rightRows001.drop 21) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 35
      (rightCached001.drop 21) (rightRows001.drop 21)
    · exact right_prefix_001_part07_checked
    · simpa only [List.drop_drop] using h024
  have h018 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 41
      (rightCached001.drop 18) (rightRows001.drop 18) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 38
      (rightCached001.drop 18) (rightRows001.drop 18)
    · exact right_prefix_001_part06_checked
    · simpa only [List.drop_drop] using h021
  have h015 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 44
      (rightCached001.drop 15) (rightRows001.drop 15) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 41
      (rightCached001.drop 15) (rightRows001.drop 15)
    · exact right_prefix_001_part05_checked
    · simpa only [List.drop_drop] using h018
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 47
      (rightCached001.drop 12) (rightRows001.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 44
      (rightCached001.drop 12) (rightRows001.drop 12)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop] using h015
  have h009 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 50
      (rightCached001.drop 9) (rightRows001.drop 9) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 47
      (rightCached001.drop 9) (rightRows001.drop 9)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop] using h012
  have h006 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 53
      (rightCached001.drop 6) (rightRows001.drop 6) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 50
      (rightCached001.drop 6) (rightRows001.drop 6)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop] using h009
  have h003 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 56
      (rightCached001.drop 3) (rightRows001.drop 3) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 53
      (rightCached001.drop 3) (rightRows001.drop 3)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop] using h006
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 59
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 56
      (rightCached001.drop 0) (rightRows001.drop 0)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop] using h003
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared26
end
