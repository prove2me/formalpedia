-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:32:03.990397+00:00
-- url     : https://prove2.me/submissions/f3fe00f6-29d2-43b1-a0c5-8c9b7fa23835

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_part09_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 225
      (PairLightPrepared39.leftCached.drop 233) (PairLightPrepared39.leftRows.drop 233) = true := by
  have h449 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 9
      (PairLightPrepared39.leftCached.drop 449) (PairLightPrepared39.leftRows.drop 449) = true := left_prefix_002_part09_checked
  have h425 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 33
      (PairLightPrepared39.leftCached.drop 425) (PairLightPrepared39.leftRows.drop 425) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 9
      (PairLightPrepared39.leftCached.drop 425) (PairLightPrepared39.leftRows.drop 425)
    · exact left_prefix_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h449
  have h401 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 57
      (PairLightPrepared39.leftCached.drop 401) (PairLightPrepared39.leftRows.drop 401) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 33
      (PairLightPrepared39.leftCached.drop 401) (PairLightPrepared39.leftRows.drop 401)
    · exact left_prefix_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h425
  have h377 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 81
      (PairLightPrepared39.leftCached.drop 377) (PairLightPrepared39.leftRows.drop 377) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 57
      (PairLightPrepared39.leftCached.drop 377) (PairLightPrepared39.leftRows.drop 377)
    · exact left_prefix_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h401
  have h353 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 105
      (PairLightPrepared39.leftCached.drop 353) (PairLightPrepared39.leftRows.drop 353) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 81
      (PairLightPrepared39.leftCached.drop 353) (PairLightPrepared39.leftRows.drop 353)
    · exact left_prefix_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h377
  have h329 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 129
      (PairLightPrepared39.leftCached.drop 329) (PairLightPrepared39.leftRows.drop 329) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 105
      (PairLightPrepared39.leftCached.drop 329) (PairLightPrepared39.leftRows.drop 329)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h353
  have h305 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 153
      (PairLightPrepared39.leftCached.drop 305) (PairLightPrepared39.leftRows.drop 305) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 129
      (PairLightPrepared39.leftCached.drop 305) (PairLightPrepared39.leftRows.drop 305)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h329
  have h281 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 177
      (PairLightPrepared39.leftCached.drop 281) (PairLightPrepared39.leftRows.drop 281) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 153
      (PairLightPrepared39.leftCached.drop 281) (PairLightPrepared39.leftRows.drop 281)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h305
  have h257 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 201
      (PairLightPrepared39.leftCached.drop 257) (PairLightPrepared39.leftRows.drop 257) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 177
      (PairLightPrepared39.leftCached.drop 257) (PairLightPrepared39.leftRows.drop 257)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h281
  have h233 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 225
      (PairLightPrepared39.leftCached.drop 233) (PairLightPrepared39.leftRows.drop 233) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared39.sieve 24 201
      (PairLightPrepared39.leftCached.drop 233) (PairLightPrepared39.leftRows.drop 233)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h257
  exact h233
end D1Bound5.PairLightAdaptivePrepared39
end
