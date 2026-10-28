-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:23:20.149401+00:00
-- url     : https://prove2.me/submissions/9f6ef000-8150-4996-bde6-ac942a9c8b2f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 164
      (PairLightPrepared5.leftCached.drop 105) (PairLightPrepared5.leftRows.drop 105) = true := by
  have h249 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 20
      (PairLightPrepared5.leftCached.drop 249) (PairLightPrepared5.leftRows.drop 249) = true := left_prefix_001_part06_checked
  have h225 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 44
      (PairLightPrepared5.leftCached.drop 225) (PairLightPrepared5.leftRows.drop 225) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 20
      (PairLightPrepared5.leftCached.drop 225) (PairLightPrepared5.leftRows.drop 225)
    · exact left_prefix_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h249
  have h201 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 68
      (PairLightPrepared5.leftCached.drop 201) (PairLightPrepared5.leftRows.drop 201) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 44
      (PairLightPrepared5.leftCached.drop 201) (PairLightPrepared5.leftRows.drop 201)
    · exact left_prefix_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h225
  have h177 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 92
      (PairLightPrepared5.leftCached.drop 177) (PairLightPrepared5.leftRows.drop 177) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 68
      (PairLightPrepared5.leftCached.drop 177) (PairLightPrepared5.leftRows.drop 177)
    · exact left_prefix_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h201
  have h153 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 116
      (PairLightPrepared5.leftCached.drop 153) (PairLightPrepared5.leftRows.drop 153) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 92
      (PairLightPrepared5.leftCached.drop 153) (PairLightPrepared5.leftRows.drop 153)
    · exact left_prefix_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h177
  have h129 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 140
      (PairLightPrepared5.leftCached.drop 129) (PairLightPrepared5.leftRows.drop 129) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 116
      (PairLightPrepared5.leftCached.drop 129) (PairLightPrepared5.leftRows.drop 129)
    · exact left_prefix_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h153
  have h105 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 164
      (PairLightPrepared5.leftCached.drop 105) (PairLightPrepared5.leftRows.drop 105) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 140
      (PairLightPrepared5.leftCached.drop 105) (PairLightPrepared5.leftRows.drop 105)
    · exact left_prefix_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h129
  exact h105
end D1Bound5.PairLightAdaptivePrepared5
end
