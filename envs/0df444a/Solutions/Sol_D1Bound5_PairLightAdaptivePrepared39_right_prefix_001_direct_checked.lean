-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:14:38.415525+00:00
-- url     : https://prove2.me/submissions/ccd32aa3-0493-4103-b4e3-e5e5c1d9e17c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 138
      (PairLightPrepared39.rightCached.drop 98) (PairLightPrepared39.rightRows.drop 98) = true := by
  have h218 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 18
      (PairLightPrepared39.rightCached.drop 218) (PairLightPrepared39.rightRows.drop 218) = true := right_prefix_001_part05_checked
  have h194 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 42
      (PairLightPrepared39.rightCached.drop 194) (PairLightPrepared39.rightRows.drop 194) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 18
      (PairLightPrepared39.rightCached.drop 194) (PairLightPrepared39.rightRows.drop 194)
    · exact right_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h218
  have h170 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 66
      (PairLightPrepared39.rightCached.drop 170) (PairLightPrepared39.rightRows.drop 170) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 42
      (PairLightPrepared39.rightCached.drop 170) (PairLightPrepared39.rightRows.drop 170)
    · exact right_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h194
  have h146 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 90
      (PairLightPrepared39.rightCached.drop 146) (PairLightPrepared39.rightRows.drop 146) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 66
      (PairLightPrepared39.rightCached.drop 146) (PairLightPrepared39.rightRows.drop 146)
    · exact right_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h170
  have h122 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 114
      (PairLightPrepared39.rightCached.drop 122) (PairLightPrepared39.rightRows.drop 122) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 90
      (PairLightPrepared39.rightCached.drop 122) (PairLightPrepared39.rightRows.drop 122)
    · exact right_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h146
  have h098 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 138
      (PairLightPrepared39.rightCached.drop 98) (PairLightPrepared39.rightRows.drop 98) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 114
      (PairLightPrepared39.rightCached.drop 98) (PairLightPrepared39.rightRows.drop 98)
    · exact right_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h122
  exact h098
end D1Bound5.PairLightAdaptivePrepared39
end
