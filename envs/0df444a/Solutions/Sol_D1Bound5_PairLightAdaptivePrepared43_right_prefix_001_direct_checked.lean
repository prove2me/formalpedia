-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:23.589551+00:00
-- url     : https://prove2.me/submissions/e2c54ee2-30e4-40b1-a62b-36d888a33c5e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_part10_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 122
      (PairLightPrepared43.rightCached.drop 92) (PairLightPrepared43.rightRows.drop 92) = true := by
  have h212 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 2
      (PairLightPrepared43.rightCached.drop 212) (PairLightPrepared43.rightRows.drop 212) = true := right_prefix_001_part10_checked
  have h200 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 14
      (PairLightPrepared43.rightCached.drop 200) (PairLightPrepared43.rightRows.drop 200) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 2
      (PairLightPrepared43.rightCached.drop 200) (PairLightPrepared43.rightRows.drop 200)
    · exact right_prefix_001_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h212
  have h188 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 26
      (PairLightPrepared43.rightCached.drop 188) (PairLightPrepared43.rightRows.drop 188) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 14
      (PairLightPrepared43.rightCached.drop 188) (PairLightPrepared43.rightRows.drop 188)
    · exact right_prefix_001_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h200
  have h176 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 38
      (PairLightPrepared43.rightCached.drop 176) (PairLightPrepared43.rightRows.drop 176) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 26
      (PairLightPrepared43.rightCached.drop 176) (PairLightPrepared43.rightRows.drop 176)
    · exact right_prefix_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h188
  have h164 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 50
      (PairLightPrepared43.rightCached.drop 164) (PairLightPrepared43.rightRows.drop 164) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 38
      (PairLightPrepared43.rightCached.drop 164) (PairLightPrepared43.rightRows.drop 164)
    · exact right_prefix_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h176
  have h152 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 62
      (PairLightPrepared43.rightCached.drop 152) (PairLightPrepared43.rightRows.drop 152) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 50
      (PairLightPrepared43.rightCached.drop 152) (PairLightPrepared43.rightRows.drop 152)
    · exact right_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h164
  have h140 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 74
      (PairLightPrepared43.rightCached.drop 140) (PairLightPrepared43.rightRows.drop 140) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 62
      (PairLightPrepared43.rightCached.drop 140) (PairLightPrepared43.rightRows.drop 140)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h152
  have h128 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 86
      (PairLightPrepared43.rightCached.drop 128) (PairLightPrepared43.rightRows.drop 128) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 74
      (PairLightPrepared43.rightCached.drop 128) (PairLightPrepared43.rightRows.drop 128)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h140
  have h116 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 98
      (PairLightPrepared43.rightCached.drop 116) (PairLightPrepared43.rightRows.drop 116) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 86
      (PairLightPrepared43.rightCached.drop 116) (PairLightPrepared43.rightRows.drop 116)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h128
  have h104 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 110
      (PairLightPrepared43.rightCached.drop 104) (PairLightPrepared43.rightRows.drop 104) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 98
      (PairLightPrepared43.rightCached.drop 104) (PairLightPrepared43.rightRows.drop 104)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h116
  have h092 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 122
      (PairLightPrepared43.rightCached.drop 92) (PairLightPrepared43.rightRows.drop 92) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 12 110
      (PairLightPrepared43.rightCached.drop 92) (PairLightPrepared43.rightRows.drop 92)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h104
  exact h092
end D1Bound5.PairLightAdaptivePrepared43
end
