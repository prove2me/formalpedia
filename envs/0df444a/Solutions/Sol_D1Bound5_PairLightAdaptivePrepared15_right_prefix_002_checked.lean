-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:28.221466+00:00
-- url     : https://prove2.me/submissions/668b3f7e-12da-4434-9e42-9ceabf917b94

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part18_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part19_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part20_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part21_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part22_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 266
      rightCached002 rightRows002 = true := by
  have h0478 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 2
      (PairLightPrepared15.rightCached.drop 478) (PairLightPrepared15.rightRows.drop 478) = true := right_parallel_002_part22_checked
  have h0466 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 14
      (PairLightPrepared15.rightCached.drop 466) (PairLightPrepared15.rightRows.drop 466) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 2
      (PairLightPrepared15.rightCached.drop 466) (PairLightPrepared15.rightRows.drop 466)
    · exact right_parallel_002_part21_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0478
  have h0454 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 26
      (PairLightPrepared15.rightCached.drop 454) (PairLightPrepared15.rightRows.drop 454) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 14
      (PairLightPrepared15.rightCached.drop 454) (PairLightPrepared15.rightRows.drop 454)
    · exact right_parallel_002_part20_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0466
  have h0442 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 38
      (PairLightPrepared15.rightCached.drop 442) (PairLightPrepared15.rightRows.drop 442) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 26
      (PairLightPrepared15.rightCached.drop 442) (PairLightPrepared15.rightRows.drop 442)
    · exact right_parallel_002_part19_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0454
  have h0430 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 50
      (PairLightPrepared15.rightCached.drop 430) (PairLightPrepared15.rightRows.drop 430) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 38
      (PairLightPrepared15.rightCached.drop 430) (PairLightPrepared15.rightRows.drop 430)
    · exact right_parallel_002_part18_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0442
  have h0418 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 62
      (PairLightPrepared15.rightCached.drop 418) (PairLightPrepared15.rightRows.drop 418) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 50
      (PairLightPrepared15.rightCached.drop 418) (PairLightPrepared15.rightRows.drop 418)
    · exact right_parallel_002_part17_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0430
  have h0406 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 74
      (PairLightPrepared15.rightCached.drop 406) (PairLightPrepared15.rightRows.drop 406) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 62
      (PairLightPrepared15.rightCached.drop 406) (PairLightPrepared15.rightRows.drop 406)
    · exact right_parallel_002_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0418
  have h0394 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 86
      (PairLightPrepared15.rightCached.drop 394) (PairLightPrepared15.rightRows.drop 394) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 74
      (PairLightPrepared15.rightCached.drop 394) (PairLightPrepared15.rightRows.drop 394)
    · exact right_parallel_002_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0406
  have h0382 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 98
      (PairLightPrepared15.rightCached.drop 382) (PairLightPrepared15.rightRows.drop 382) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 86
      (PairLightPrepared15.rightCached.drop 382) (PairLightPrepared15.rightRows.drop 382)
    · exact right_parallel_002_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0394
  have h0370 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 110
      (PairLightPrepared15.rightCached.drop 370) (PairLightPrepared15.rightRows.drop 370) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 98
      (PairLightPrepared15.rightCached.drop 370) (PairLightPrepared15.rightRows.drop 370)
    · exact right_parallel_002_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0382
  have h0358 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 122
      (PairLightPrepared15.rightCached.drop 358) (PairLightPrepared15.rightRows.drop 358) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 110
      (PairLightPrepared15.rightCached.drop 358) (PairLightPrepared15.rightRows.drop 358)
    · exact right_parallel_002_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0370
  have h0346 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 134
      (PairLightPrepared15.rightCached.drop 346) (PairLightPrepared15.rightRows.drop 346) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 122
      (PairLightPrepared15.rightCached.drop 346) (PairLightPrepared15.rightRows.drop 346)
    · exact right_parallel_002_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0358
  have h0334 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 146
      (PairLightPrepared15.rightCached.drop 334) (PairLightPrepared15.rightRows.drop 334) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 134
      (PairLightPrepared15.rightCached.drop 334) (PairLightPrepared15.rightRows.drop 334)
    · exact right_parallel_002_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0346
  have h0322 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 158
      (PairLightPrepared15.rightCached.drop 322) (PairLightPrepared15.rightRows.drop 322) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 146
      (PairLightPrepared15.rightCached.drop 322) (PairLightPrepared15.rightRows.drop 322)
    · exact right_parallel_002_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0334
  have h0310 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 170
      (PairLightPrepared15.rightCached.drop 310) (PairLightPrepared15.rightRows.drop 310) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 158
      (PairLightPrepared15.rightCached.drop 310) (PairLightPrepared15.rightRows.drop 310)
    · exact right_parallel_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0322
  have h0298 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 182
      (PairLightPrepared15.rightCached.drop 298) (PairLightPrepared15.rightRows.drop 298) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 170
      (PairLightPrepared15.rightCached.drop 298) (PairLightPrepared15.rightRows.drop 298)
    · exact right_parallel_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0310
  have h0286 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 194
      (PairLightPrepared15.rightCached.drop 286) (PairLightPrepared15.rightRows.drop 286) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 182
      (PairLightPrepared15.rightCached.drop 286) (PairLightPrepared15.rightRows.drop 286)
    · exact right_parallel_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0298
  have h0274 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 206
      (PairLightPrepared15.rightCached.drop 274) (PairLightPrepared15.rightRows.drop 274) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 194
      (PairLightPrepared15.rightCached.drop 274) (PairLightPrepared15.rightRows.drop 274)
    · exact right_parallel_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0286
  have h0262 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 218
      (PairLightPrepared15.rightCached.drop 262) (PairLightPrepared15.rightRows.drop 262) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 206
      (PairLightPrepared15.rightCached.drop 262) (PairLightPrepared15.rightRows.drop 262)
    · exact right_parallel_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0274
  have h0250 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 230
      (PairLightPrepared15.rightCached.drop 250) (PairLightPrepared15.rightRows.drop 250) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 218
      (PairLightPrepared15.rightCached.drop 250) (PairLightPrepared15.rightRows.drop 250)
    · exact right_parallel_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0262
  have h0238 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 242
      (PairLightPrepared15.rightCached.drop 238) (PairLightPrepared15.rightRows.drop 238) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 230
      (PairLightPrepared15.rightCached.drop 238) (PairLightPrepared15.rightRows.drop 238)
    · exact right_parallel_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0250
  have h0226 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 254
      (PairLightPrepared15.rightCached.drop 226) (PairLightPrepared15.rightRows.drop 226) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 242
      (PairLightPrepared15.rightCached.drop 226) (PairLightPrepared15.rightRows.drop 226)
    · exact right_parallel_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0238
  have h0214 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 266
      (PairLightPrepared15.rightCached.drop 214) (PairLightPrepared15.rightRows.drop 214) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared15.sieve 12 254
      (PairLightPrepared15.rightCached.drop 214) (PairLightPrepared15.rightRows.drop 214)
    · exact right_parallel_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0226
  exact h0214

end D1Bound5.PairLightAdaptivePrepared15
end
