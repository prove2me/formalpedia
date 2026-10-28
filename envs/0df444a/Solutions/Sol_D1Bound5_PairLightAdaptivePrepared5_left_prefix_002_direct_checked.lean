-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:24:18.672929+00:00
-- url     : https://prove2.me/submissions/f85197f1-349b-4a5c-9377-91b3a8aa27bd

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_002_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 162
      (PairLightPrepared5.leftCached.drop 269) (PairLightPrepared5.leftRows.drop 269) = true := by
  have h413 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 18
      (PairLightPrepared5.leftCached.drop 413) (PairLightPrepared5.leftRows.drop 413) = true := left_prefix_002_part06_checked
  have h389 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 42
      (PairLightPrepared5.leftCached.drop 389) (PairLightPrepared5.leftRows.drop 389) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 18
      (PairLightPrepared5.leftCached.drop 389) (PairLightPrepared5.leftRows.drop 389)
    · exact left_prefix_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h413
  have h365 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 66
      (PairLightPrepared5.leftCached.drop 365) (PairLightPrepared5.leftRows.drop 365) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 42
      (PairLightPrepared5.leftCached.drop 365) (PairLightPrepared5.leftRows.drop 365)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h389
  have h341 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 90
      (PairLightPrepared5.leftCached.drop 341) (PairLightPrepared5.leftRows.drop 341) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 66
      (PairLightPrepared5.leftCached.drop 341) (PairLightPrepared5.leftRows.drop 341)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h365
  have h317 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 114
      (PairLightPrepared5.leftCached.drop 317) (PairLightPrepared5.leftRows.drop 317) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 90
      (PairLightPrepared5.leftCached.drop 317) (PairLightPrepared5.leftRows.drop 317)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h341
  have h293 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 138
      (PairLightPrepared5.leftCached.drop 293) (PairLightPrepared5.leftRows.drop 293) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 114
      (PairLightPrepared5.leftCached.drop 293) (PairLightPrepared5.leftRows.drop 293)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h317
  have h269 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 162
      (PairLightPrepared5.leftCached.drop 269) (PairLightPrepared5.leftRows.drop 269) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared5.sieve 24 138
      (PairLightPrepared5.leftCached.drop 269) (PairLightPrepared5.leftRows.drop 269)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h293
  exact h269
end D1Bound5.PairLightAdaptivePrepared5
end
