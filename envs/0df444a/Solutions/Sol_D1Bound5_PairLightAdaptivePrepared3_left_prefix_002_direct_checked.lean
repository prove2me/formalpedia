-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:15.409158+00:00
-- url     : https://prove2.me/submissions/62fc06bc-e774-4484-a6ba-53913cc2ce8e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 102
      (PairLightPrepared3.leftCached.drop 311) (PairLightPrepared3.leftRows.drop 311) = true := by
  have h407 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 6
      (PairLightPrepared3.leftCached.drop 407) (PairLightPrepared3.leftRows.drop 407) = true := left_prefix_002_part04_checked
  have h383 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 30
      (PairLightPrepared3.leftCached.drop 383) (PairLightPrepared3.leftRows.drop 383) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 6
      (PairLightPrepared3.leftCached.drop 383) (PairLightPrepared3.leftRows.drop 383)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h407
  have h359 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 54
      (PairLightPrepared3.leftCached.drop 359) (PairLightPrepared3.leftRows.drop 359) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 30
      (PairLightPrepared3.leftCached.drop 359) (PairLightPrepared3.leftRows.drop 359)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h383
  have h335 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 78
      (PairLightPrepared3.leftCached.drop 335) (PairLightPrepared3.leftRows.drop 335) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 54
      (PairLightPrepared3.leftCached.drop 335) (PairLightPrepared3.leftRows.drop 335)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h359
  have h311 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 102
      (PairLightPrepared3.leftCached.drop 311) (PairLightPrepared3.leftRows.drop 311) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared3.sieve 24 78
      (PairLightPrepared3.leftCached.drop 311) (PairLightPrepared3.leftRows.drop 311)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h335
  exact h311
end D1Bound5.PairLightAdaptivePrepared3
end
