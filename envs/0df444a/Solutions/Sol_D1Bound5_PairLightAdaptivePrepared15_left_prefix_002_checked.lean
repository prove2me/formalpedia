-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:26:32.544204+00:00
-- url     : https://prove2.me/submissions/00d8dfb7-e477-41af-bd24-d234526c71d0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part18_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part19_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part20_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part21_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part22_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 267
      leftCached002 leftRows002 = true := by
  have h0478 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 3
      (PairLightPrepared15.leftCached.drop 478) (PairLightPrepared15.leftRows.drop 478) = true := left_parallel_002_part22_checked
  have h0466 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 15
      (PairLightPrepared15.leftCached.drop 466) (PairLightPrepared15.leftRows.drop 466) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 3
      (PairLightPrepared15.leftCached.drop 466) (PairLightPrepared15.leftRows.drop 466)
    · exact left_parallel_002_part21_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0478
  have h0454 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 27
      (PairLightPrepared15.leftCached.drop 454) (PairLightPrepared15.leftRows.drop 454) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 15
      (PairLightPrepared15.leftCached.drop 454) (PairLightPrepared15.leftRows.drop 454)
    · exact left_parallel_002_part20_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0466
  have h0442 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 39
      (PairLightPrepared15.leftCached.drop 442) (PairLightPrepared15.leftRows.drop 442) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 27
      (PairLightPrepared15.leftCached.drop 442) (PairLightPrepared15.leftRows.drop 442)
    · exact left_parallel_002_part19_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0454
  have h0430 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 51
      (PairLightPrepared15.leftCached.drop 430) (PairLightPrepared15.leftRows.drop 430) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 39
      (PairLightPrepared15.leftCached.drop 430) (PairLightPrepared15.leftRows.drop 430)
    · exact left_parallel_002_part18_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0442
  have h0418 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 63
      (PairLightPrepared15.leftCached.drop 418) (PairLightPrepared15.leftRows.drop 418) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 51
      (PairLightPrepared15.leftCached.drop 418) (PairLightPrepared15.leftRows.drop 418)
    · exact left_parallel_002_part17_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0430
  have h0406 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 75
      (PairLightPrepared15.leftCached.drop 406) (PairLightPrepared15.leftRows.drop 406) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 63
      (PairLightPrepared15.leftCached.drop 406) (PairLightPrepared15.leftRows.drop 406)
    · exact left_parallel_002_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0418
  have h0394 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 87
      (PairLightPrepared15.leftCached.drop 394) (PairLightPrepared15.leftRows.drop 394) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 75
      (PairLightPrepared15.leftCached.drop 394) (PairLightPrepared15.leftRows.drop 394)
    · exact left_parallel_002_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0406
  have h0382 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 99
      (PairLightPrepared15.leftCached.drop 382) (PairLightPrepared15.leftRows.drop 382) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 87
      (PairLightPrepared15.leftCached.drop 382) (PairLightPrepared15.leftRows.drop 382)
    · exact left_parallel_002_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0394
  have h0370 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 111
      (PairLightPrepared15.leftCached.drop 370) (PairLightPrepared15.leftRows.drop 370) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 99
      (PairLightPrepared15.leftCached.drop 370) (PairLightPrepared15.leftRows.drop 370)
    · exact left_parallel_002_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0382
  have h0358 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 123
      (PairLightPrepared15.leftCached.drop 358) (PairLightPrepared15.leftRows.drop 358) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 111
      (PairLightPrepared15.leftCached.drop 358) (PairLightPrepared15.leftRows.drop 358)
    · exact left_parallel_002_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0370
  have h0346 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 135
      (PairLightPrepared15.leftCached.drop 346) (PairLightPrepared15.leftRows.drop 346) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 123
      (PairLightPrepared15.leftCached.drop 346) (PairLightPrepared15.leftRows.drop 346)
    · exact left_parallel_002_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0358
  have h0334 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 147
      (PairLightPrepared15.leftCached.drop 334) (PairLightPrepared15.leftRows.drop 334) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 135
      (PairLightPrepared15.leftCached.drop 334) (PairLightPrepared15.leftRows.drop 334)
    · exact left_parallel_002_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0346
  have h0322 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 159
      (PairLightPrepared15.leftCached.drop 322) (PairLightPrepared15.leftRows.drop 322) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 147
      (PairLightPrepared15.leftCached.drop 322) (PairLightPrepared15.leftRows.drop 322)
    · exact left_parallel_002_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0334
  have h0310 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 171
      (PairLightPrepared15.leftCached.drop 310) (PairLightPrepared15.leftRows.drop 310) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 159
      (PairLightPrepared15.leftCached.drop 310) (PairLightPrepared15.leftRows.drop 310)
    · exact left_parallel_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0322
  have h0298 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 183
      (PairLightPrepared15.leftCached.drop 298) (PairLightPrepared15.leftRows.drop 298) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 171
      (PairLightPrepared15.leftCached.drop 298) (PairLightPrepared15.leftRows.drop 298)
    · exact left_parallel_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0310
  have h0286 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 195
      (PairLightPrepared15.leftCached.drop 286) (PairLightPrepared15.leftRows.drop 286) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 183
      (PairLightPrepared15.leftCached.drop 286) (PairLightPrepared15.leftRows.drop 286)
    · exact left_parallel_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0298
  have h0274 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 207
      (PairLightPrepared15.leftCached.drop 274) (PairLightPrepared15.leftRows.drop 274) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 195
      (PairLightPrepared15.leftCached.drop 274) (PairLightPrepared15.leftRows.drop 274)
    · exact left_parallel_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0286
  have h0262 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 219
      (PairLightPrepared15.leftCached.drop 262) (PairLightPrepared15.leftRows.drop 262) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 207
      (PairLightPrepared15.leftCached.drop 262) (PairLightPrepared15.leftRows.drop 262)
    · exact left_parallel_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0274
  have h0250 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 231
      (PairLightPrepared15.leftCached.drop 250) (PairLightPrepared15.leftRows.drop 250) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 219
      (PairLightPrepared15.leftCached.drop 250) (PairLightPrepared15.leftRows.drop 250)
    · exact left_parallel_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0262
  have h0238 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 243
      (PairLightPrepared15.leftCached.drop 238) (PairLightPrepared15.leftRows.drop 238) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 231
      (PairLightPrepared15.leftCached.drop 238) (PairLightPrepared15.leftRows.drop 238)
    · exact left_parallel_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0250
  have h0226 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 255
      (PairLightPrepared15.leftCached.drop 226) (PairLightPrepared15.leftRows.drop 226) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 243
      (PairLightPrepared15.leftCached.drop 226) (PairLightPrepared15.leftRows.drop 226)
    · exact left_parallel_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0238
  have h0214 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 267
      (PairLightPrepared15.leftCached.drop 214) (PairLightPrepared15.leftRows.drop 214) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 255
      (PairLightPrepared15.leftCached.drop 214) (PairLightPrepared15.leftRows.drop 214)
    · exact left_parallel_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0226
  exact h0214

end D1Bound5.PairLightAdaptivePrepared15
end
