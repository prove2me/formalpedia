-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:14.525983+00:00
-- url     : https://prove2.me/submissions/cc658e4f-06ef-4c3e-a190-d0a4f855253d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_000_part17_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000

/-- Heads 0 through 53; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 54
      leftCached000 leftRows000 = true := by
  have h051 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 51) (leftRows000.drop 51) = true := left_prefix_000_part17_checked
  have h048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 6
      (leftCached000.drop 48) (leftRows000.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 3
      (leftCached000.drop 48) (leftRows000.drop 48)
    · exact left_prefix_000_part16_checked
    · simpa only [List.drop_drop] using h051
  have h045 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 9
      (leftCached000.drop 45) (leftRows000.drop 45) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 6
      (leftCached000.drop 45) (leftRows000.drop 45)
    · exact left_prefix_000_part15_checked
    · simpa only [List.drop_drop] using h048
  have h042 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached000.drop 42) (leftRows000.drop 42) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 9
      (leftCached000.drop 42) (leftRows000.drop 42)
    · exact left_prefix_000_part14_checked
    · simpa only [List.drop_drop] using h045
  have h039 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 15
      (leftCached000.drop 39) (leftRows000.drop 39) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 12
      (leftCached000.drop 39) (leftRows000.drop 39)
    · exact left_prefix_000_part13_checked
    · simpa only [List.drop_drop] using h042
  have h036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 18
      (leftCached000.drop 36) (leftRows000.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 15
      (leftCached000.drop 36) (leftRows000.drop 36)
    · exact left_prefix_000_part12_checked
    · simpa only [List.drop_drop] using h039
  have h033 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 21
      (leftCached000.drop 33) (leftRows000.drop 33) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 18
      (leftCached000.drop 33) (leftRows000.drop 33)
    · exact left_prefix_000_part11_checked
    · simpa only [List.drop_drop] using h036
  have h030 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 24
      (leftCached000.drop 30) (leftRows000.drop 30) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 21
      (leftCached000.drop 30) (leftRows000.drop 30)
    · exact left_prefix_000_part10_checked
    · simpa only [List.drop_drop] using h033
  have h027 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 27
      (leftCached000.drop 27) (leftRows000.drop 27) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 24
      (leftCached000.drop 27) (leftRows000.drop 27)
    · exact left_prefix_000_part09_checked
    · simpa only [List.drop_drop] using h030
  have h024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 30
      (leftCached000.drop 24) (leftRows000.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 27
      (leftCached000.drop 24) (leftRows000.drop 24)
    · exact left_prefix_000_part08_checked
    · simpa only [List.drop_drop] using h027
  have h021 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 33
      (leftCached000.drop 21) (leftRows000.drop 21) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 30
      (leftCached000.drop 21) (leftRows000.drop 21)
    · exact left_prefix_000_part07_checked
    · simpa only [List.drop_drop] using h024
  have h018 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 36
      (leftCached000.drop 18) (leftRows000.drop 18) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 33
      (leftCached000.drop 18) (leftRows000.drop 18)
    · exact left_prefix_000_part06_checked
    · simpa only [List.drop_drop] using h021
  have h015 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 39
      (leftCached000.drop 15) (leftRows000.drop 15) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 36
      (leftCached000.drop 15) (leftRows000.drop 15)
    · exact left_prefix_000_part05_checked
    · simpa only [List.drop_drop] using h018
  have h012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 42
      (leftCached000.drop 12) (leftRows000.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 39
      (leftCached000.drop 12) (leftRows000.drop 12)
    · exact left_prefix_000_part04_checked
    · simpa only [List.drop_drop] using h015
  have h009 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 45
      (leftCached000.drop 9) (leftRows000.drop 9) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 42
      (leftCached000.drop 9) (leftRows000.drop 9)
    · exact left_prefix_000_part03_checked
    · simpa only [List.drop_drop] using h012
  have h006 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 48
      (leftCached000.drop 6) (leftRows000.drop 6) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 45
      (leftCached000.drop 6) (leftRows000.drop 6)
    · exact left_prefix_000_part02_checked
    · simpa only [List.drop_drop] using h009
  have h003 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 51
      (leftCached000.drop 3) (leftRows000.drop 3) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 48
      (leftCached000.drop 3) (leftRows000.drop 3)
    · exact left_prefix_000_part01_checked
    · simpa only [List.drop_drop] using h006
  have h000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 54
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared26.sieve 3 51
      (leftCached000.drop 0) (leftRows000.drop 0)
    · exact left_prefix_000_part00_checked
    · simpa only [List.drop_drop] using h003
  simpa only [List.drop_zero] using h000

end D1Bound5.PairLightAdaptivePrepared26
end
