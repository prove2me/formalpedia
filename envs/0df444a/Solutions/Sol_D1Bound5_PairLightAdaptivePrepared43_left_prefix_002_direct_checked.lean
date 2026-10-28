-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:18:11.622316+00:00
-- url     : https://prove2.me/submissions/98b2aed6-bc00-47e2-9147-e57312eb6189

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_part11_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 270
      (PairLightPrepared43.leftCached.drop 212) (PairLightPrepared43.leftRows.drop 212) = true := by
  have h476 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 6
      (PairLightPrepared43.leftCached.drop 476) (PairLightPrepared43.leftRows.drop 476) = true := left_prefix_002_part11_checked
  have h452 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 30
      (PairLightPrepared43.leftCached.drop 452) (PairLightPrepared43.leftRows.drop 452) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 6
      (PairLightPrepared43.leftCached.drop 452) (PairLightPrepared43.leftRows.drop 452)
    · exact left_prefix_002_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h476
  have h428 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 54
      (PairLightPrepared43.leftCached.drop 428) (PairLightPrepared43.leftRows.drop 428) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 30
      (PairLightPrepared43.leftCached.drop 428) (PairLightPrepared43.leftRows.drop 428)
    · exact left_prefix_002_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h452
  have h404 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 78
      (PairLightPrepared43.leftCached.drop 404) (PairLightPrepared43.leftRows.drop 404) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 54
      (PairLightPrepared43.leftCached.drop 404) (PairLightPrepared43.leftRows.drop 404)
    · exact left_prefix_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h428
  have h380 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 102
      (PairLightPrepared43.leftCached.drop 380) (PairLightPrepared43.leftRows.drop 380) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 78
      (PairLightPrepared43.leftCached.drop 380) (PairLightPrepared43.leftRows.drop 380)
    · exact left_prefix_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h404
  have h356 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 126
      (PairLightPrepared43.leftCached.drop 356) (PairLightPrepared43.leftRows.drop 356) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 102
      (PairLightPrepared43.leftCached.drop 356) (PairLightPrepared43.leftRows.drop 356)
    · exact left_prefix_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h380
  have h332 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 150
      (PairLightPrepared43.leftCached.drop 332) (PairLightPrepared43.leftRows.drop 332) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 126
      (PairLightPrepared43.leftCached.drop 332) (PairLightPrepared43.leftRows.drop 332)
    · exact left_prefix_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h356
  have h308 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 174
      (PairLightPrepared43.leftCached.drop 308) (PairLightPrepared43.leftRows.drop 308) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 150
      (PairLightPrepared43.leftCached.drop 308) (PairLightPrepared43.leftRows.drop 308)
    · exact left_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h332
  have h284 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 198
      (PairLightPrepared43.leftCached.drop 284) (PairLightPrepared43.leftRows.drop 284) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 174
      (PairLightPrepared43.leftCached.drop 284) (PairLightPrepared43.leftRows.drop 284)
    · exact left_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h308
  have h260 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 222
      (PairLightPrepared43.leftCached.drop 260) (PairLightPrepared43.leftRows.drop 260) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 198
      (PairLightPrepared43.leftCached.drop 260) (PairLightPrepared43.leftRows.drop 260)
    · exact left_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h284
  have h236 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 246
      (PairLightPrepared43.leftCached.drop 236) (PairLightPrepared43.leftRows.drop 236) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 222
      (PairLightPrepared43.leftCached.drop 236) (PairLightPrepared43.leftRows.drop 236)
    · exact left_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h260
  have h212 : pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 270
      (PairLightPrepared43.leftCached.drop 212) (PairLightPrepared43.leftRows.drop 212) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 3 PairLightPrepared43.sieve 24 246
      (PairLightPrepared43.leftCached.drop 212) (PairLightPrepared43.leftRows.drop 212)
    · exact left_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h236
  exact h212
end D1Bound5.PairLightAdaptivePrepared43
end
