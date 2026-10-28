-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:30:48.080247+00:00
-- url     : https://prove2.me/submissions/60af8e3b-3d57-4710-af37-cfb7c43655fb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_part10_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 121
      (PairLightPrepared43.leftCached.drop 91) (PairLightPrepared43.leftRows.drop 91) = true := by
  have h211 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 1
      (PairLightPrepared43.leftCached.drop 211) (PairLightPrepared43.leftRows.drop 211) = true := left_prefix_001_part10_checked
  have h199 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 13
      (PairLightPrepared43.leftCached.drop 199) (PairLightPrepared43.leftRows.drop 199) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 1
      (PairLightPrepared43.leftCached.drop 199) (PairLightPrepared43.leftRows.drop 199)
    · exact left_prefix_001_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h211
  have h187 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 25
      (PairLightPrepared43.leftCached.drop 187) (PairLightPrepared43.leftRows.drop 187) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 13
      (PairLightPrepared43.leftCached.drop 187) (PairLightPrepared43.leftRows.drop 187)
    · exact left_prefix_001_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h199
  have h175 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 37
      (PairLightPrepared43.leftCached.drop 175) (PairLightPrepared43.leftRows.drop 175) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 25
      (PairLightPrepared43.leftCached.drop 175) (PairLightPrepared43.leftRows.drop 175)
    · exact left_prefix_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h187
  have h163 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 49
      (PairLightPrepared43.leftCached.drop 163) (PairLightPrepared43.leftRows.drop 163) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 37
      (PairLightPrepared43.leftCached.drop 163) (PairLightPrepared43.leftRows.drop 163)
    · exact left_prefix_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h175
  have h151 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 61
      (PairLightPrepared43.leftCached.drop 151) (PairLightPrepared43.leftRows.drop 151) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 49
      (PairLightPrepared43.leftCached.drop 151) (PairLightPrepared43.leftRows.drop 151)
    · exact left_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h163
  have h139 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 73
      (PairLightPrepared43.leftCached.drop 139) (PairLightPrepared43.leftRows.drop 139) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 61
      (PairLightPrepared43.leftCached.drop 139) (PairLightPrepared43.leftRows.drop 139)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h151
  have h127 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 85
      (PairLightPrepared43.leftCached.drop 127) (PairLightPrepared43.leftRows.drop 127) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 73
      (PairLightPrepared43.leftCached.drop 127) (PairLightPrepared43.leftRows.drop 127)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h139
  have h115 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 97
      (PairLightPrepared43.leftCached.drop 115) (PairLightPrepared43.leftRows.drop 115) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 85
      (PairLightPrepared43.leftCached.drop 115) (PairLightPrepared43.leftRows.drop 115)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h127
  have h103 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 109
      (PairLightPrepared43.leftCached.drop 103) (PairLightPrepared43.leftRows.drop 103) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 97
      (PairLightPrepared43.leftCached.drop 103) (PairLightPrepared43.leftRows.drop 103)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h115
  have h091 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 121
      (PairLightPrepared43.leftCached.drop 91) (PairLightPrepared43.leftRows.drop 91) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 109
      (PairLightPrepared43.leftCached.drop 91) (PairLightPrepared43.leftRows.drop 91)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h103
  exact h091
end D1Bound5.PairLightAdaptivePrepared43
end
