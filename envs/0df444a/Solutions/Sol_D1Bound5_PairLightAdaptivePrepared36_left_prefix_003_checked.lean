-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_prefix_003_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:30:56.608369+00:00
-- url     : https://prove2.me/submissions/ec2ab790-342c-4706-8d8b-6fcb2a247f31

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part18_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part19_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part20_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part21_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_003_part22_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 275
      leftCached003 leftRows003 = true := by
  have h0550 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 11
      (PairLightPrepared36.leftCached.drop 550) (PairLightPrepared36.leftRows.drop 550) = true := left_parallel_003_part22_checked
  have h0538 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 23
      (PairLightPrepared36.leftCached.drop 538) (PairLightPrepared36.leftRows.drop 538) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 11
      (PairLightPrepared36.leftCached.drop 538) (PairLightPrepared36.leftRows.drop 538)
    · exact left_parallel_003_part21_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0550
  have h0526 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 35
      (PairLightPrepared36.leftCached.drop 526) (PairLightPrepared36.leftRows.drop 526) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 23
      (PairLightPrepared36.leftCached.drop 526) (PairLightPrepared36.leftRows.drop 526)
    · exact left_parallel_003_part20_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0538
  have h0514 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 47
      (PairLightPrepared36.leftCached.drop 514) (PairLightPrepared36.leftRows.drop 514) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 35
      (PairLightPrepared36.leftCached.drop 514) (PairLightPrepared36.leftRows.drop 514)
    · exact left_parallel_003_part19_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0526
  have h0502 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 59
      (PairLightPrepared36.leftCached.drop 502) (PairLightPrepared36.leftRows.drop 502) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 47
      (PairLightPrepared36.leftCached.drop 502) (PairLightPrepared36.leftRows.drop 502)
    · exact left_parallel_003_part18_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0514
  have h0490 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 71
      (PairLightPrepared36.leftCached.drop 490) (PairLightPrepared36.leftRows.drop 490) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 59
      (PairLightPrepared36.leftCached.drop 490) (PairLightPrepared36.leftRows.drop 490)
    · exact left_parallel_003_part17_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0502
  have h0478 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 83
      (PairLightPrepared36.leftCached.drop 478) (PairLightPrepared36.leftRows.drop 478) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 71
      (PairLightPrepared36.leftCached.drop 478) (PairLightPrepared36.leftRows.drop 478)
    · exact left_parallel_003_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0490
  have h0466 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 95
      (PairLightPrepared36.leftCached.drop 466) (PairLightPrepared36.leftRows.drop 466) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 83
      (PairLightPrepared36.leftCached.drop 466) (PairLightPrepared36.leftRows.drop 466)
    · exact left_parallel_003_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0478
  have h0454 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 107
      (PairLightPrepared36.leftCached.drop 454) (PairLightPrepared36.leftRows.drop 454) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 95
      (PairLightPrepared36.leftCached.drop 454) (PairLightPrepared36.leftRows.drop 454)
    · exact left_parallel_003_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0466
  have h0442 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 119
      (PairLightPrepared36.leftCached.drop 442) (PairLightPrepared36.leftRows.drop 442) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 107
      (PairLightPrepared36.leftCached.drop 442) (PairLightPrepared36.leftRows.drop 442)
    · exact left_parallel_003_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0454
  have h0430 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 131
      (PairLightPrepared36.leftCached.drop 430) (PairLightPrepared36.leftRows.drop 430) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 119
      (PairLightPrepared36.leftCached.drop 430) (PairLightPrepared36.leftRows.drop 430)
    · exact left_parallel_003_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0442
  have h0418 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 143
      (PairLightPrepared36.leftCached.drop 418) (PairLightPrepared36.leftRows.drop 418) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 131
      (PairLightPrepared36.leftCached.drop 418) (PairLightPrepared36.leftRows.drop 418)
    · exact left_parallel_003_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0430
  have h0406 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 155
      (PairLightPrepared36.leftCached.drop 406) (PairLightPrepared36.leftRows.drop 406) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 143
      (PairLightPrepared36.leftCached.drop 406) (PairLightPrepared36.leftRows.drop 406)
    · exact left_parallel_003_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0418
  have h0394 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 167
      (PairLightPrepared36.leftCached.drop 394) (PairLightPrepared36.leftRows.drop 394) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 155
      (PairLightPrepared36.leftCached.drop 394) (PairLightPrepared36.leftRows.drop 394)
    · exact left_parallel_003_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0406
  have h0382 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 179
      (PairLightPrepared36.leftCached.drop 382) (PairLightPrepared36.leftRows.drop 382) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 167
      (PairLightPrepared36.leftCached.drop 382) (PairLightPrepared36.leftRows.drop 382)
    · exact left_parallel_003_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0394
  have h0370 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 191
      (PairLightPrepared36.leftCached.drop 370) (PairLightPrepared36.leftRows.drop 370) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 179
      (PairLightPrepared36.leftCached.drop 370) (PairLightPrepared36.leftRows.drop 370)
    · exact left_parallel_003_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0382
  have h0358 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 203
      (PairLightPrepared36.leftCached.drop 358) (PairLightPrepared36.leftRows.drop 358) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 191
      (PairLightPrepared36.leftCached.drop 358) (PairLightPrepared36.leftRows.drop 358)
    · exact left_parallel_003_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0370
  have h0346 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 215
      (PairLightPrepared36.leftCached.drop 346) (PairLightPrepared36.leftRows.drop 346) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 203
      (PairLightPrepared36.leftCached.drop 346) (PairLightPrepared36.leftRows.drop 346)
    · exact left_parallel_003_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0358
  have h0334 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 227
      (PairLightPrepared36.leftCached.drop 334) (PairLightPrepared36.leftRows.drop 334) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 215
      (PairLightPrepared36.leftCached.drop 334) (PairLightPrepared36.leftRows.drop 334)
    · exact left_parallel_003_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0346
  have h0322 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 239
      (PairLightPrepared36.leftCached.drop 322) (PairLightPrepared36.leftRows.drop 322) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 227
      (PairLightPrepared36.leftCached.drop 322) (PairLightPrepared36.leftRows.drop 322)
    · exact left_parallel_003_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0334
  have h0310 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 251
      (PairLightPrepared36.leftCached.drop 310) (PairLightPrepared36.leftRows.drop 310) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 239
      (PairLightPrepared36.leftCached.drop 310) (PairLightPrepared36.leftRows.drop 310)
    · exact left_parallel_003_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0322
  have h0298 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 263
      (PairLightPrepared36.leftCached.drop 298) (PairLightPrepared36.leftRows.drop 298) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 251
      (PairLightPrepared36.leftCached.drop 298) (PairLightPrepared36.leftRows.drop 298)
    · exact left_parallel_003_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0310
  have h0286 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 275
      (PairLightPrepared36.leftCached.drop 286) (PairLightPrepared36.leftRows.drop 286) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 263
      (PairLightPrepared36.leftCached.drop 286) (PairLightPrepared36.leftRows.drop 286)
    · exact left_parallel_003_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0298
  exact h0286

end D1Bound5.PairLightAdaptivePrepared36
end
