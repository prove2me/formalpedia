-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:25.464176+00:00
-- url     : https://prove2.me/submissions/87e3d7a6-a215-47d3-942b-95463c5664d0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 164
      (PairLightPrepared7.leftCached.drop 268) (PairLightPrepared7.leftRows.drop 268) = true := by
  have h412 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 20
      (PairLightPrepared7.leftCached.drop 412) (PairLightPrepared7.leftRows.drop 412) = true := left_prefix_002_part06_checked
  have h388 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 44
      (PairLightPrepared7.leftCached.drop 388) (PairLightPrepared7.leftRows.drop 388) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 20
      (PairLightPrepared7.leftCached.drop 388) (PairLightPrepared7.leftRows.drop 388)
    · exact left_prefix_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h412
  have h364 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 68
      (PairLightPrepared7.leftCached.drop 364) (PairLightPrepared7.leftRows.drop 364) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 44
      (PairLightPrepared7.leftCached.drop 364) (PairLightPrepared7.leftRows.drop 364)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h388
  have h340 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 92
      (PairLightPrepared7.leftCached.drop 340) (PairLightPrepared7.leftRows.drop 340) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 68
      (PairLightPrepared7.leftCached.drop 340) (PairLightPrepared7.leftRows.drop 340)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h364
  have h316 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 116
      (PairLightPrepared7.leftCached.drop 316) (PairLightPrepared7.leftRows.drop 316) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 92
      (PairLightPrepared7.leftCached.drop 316) (PairLightPrepared7.leftRows.drop 316)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h340
  have h292 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 140
      (PairLightPrepared7.leftCached.drop 292) (PairLightPrepared7.leftRows.drop 292) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 116
      (PairLightPrepared7.leftCached.drop 292) (PairLightPrepared7.leftRows.drop 292)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h316
  have h268 : pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 164
      (PairLightPrepared7.leftCached.drop 268) (PairLightPrepared7.leftRows.drop 268) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 1 PairLightPrepared7.sieve 24 140
      (PairLightPrepared7.leftCached.drop 268) (PairLightPrepared7.leftRows.drop 268)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h292
  exact h268
end D1Bound5.PairLightAdaptivePrepared7
end
