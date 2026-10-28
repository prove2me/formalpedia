-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:33.009131+00:00
-- url     : https://prove2.me/submissions/01d53f2f-d773-4a3a-bf21-662045400599

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_002_part17_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 215
      rightCached002 rightRows002 = true := by
  have h0406 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 11
      (PairLightPrepared14.rightCached.drop 406) (PairLightPrepared14.rightRows.drop 406) = true := right_parallel_002_part17_checked
  have h0394 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 23
      (PairLightPrepared14.rightCached.drop 394) (PairLightPrepared14.rightRows.drop 394) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 11
      (PairLightPrepared14.rightCached.drop 394) (PairLightPrepared14.rightRows.drop 394)
    · exact right_parallel_002_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0406
  have h0382 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 35
      (PairLightPrepared14.rightCached.drop 382) (PairLightPrepared14.rightRows.drop 382) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 23
      (PairLightPrepared14.rightCached.drop 382) (PairLightPrepared14.rightRows.drop 382)
    · exact right_parallel_002_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0394
  have h0370 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 47
      (PairLightPrepared14.rightCached.drop 370) (PairLightPrepared14.rightRows.drop 370) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 35
      (PairLightPrepared14.rightCached.drop 370) (PairLightPrepared14.rightRows.drop 370)
    · exact right_parallel_002_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0382
  have h0358 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 59
      (PairLightPrepared14.rightCached.drop 358) (PairLightPrepared14.rightRows.drop 358) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 47
      (PairLightPrepared14.rightCached.drop 358) (PairLightPrepared14.rightRows.drop 358)
    · exact right_parallel_002_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0370
  have h0346 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 71
      (PairLightPrepared14.rightCached.drop 346) (PairLightPrepared14.rightRows.drop 346) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 59
      (PairLightPrepared14.rightCached.drop 346) (PairLightPrepared14.rightRows.drop 346)
    · exact right_parallel_002_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0358
  have h0334 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 83
      (PairLightPrepared14.rightCached.drop 334) (PairLightPrepared14.rightRows.drop 334) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 71
      (PairLightPrepared14.rightCached.drop 334) (PairLightPrepared14.rightRows.drop 334)
    · exact right_parallel_002_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0346
  have h0322 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 95
      (PairLightPrepared14.rightCached.drop 322) (PairLightPrepared14.rightRows.drop 322) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 83
      (PairLightPrepared14.rightCached.drop 322) (PairLightPrepared14.rightRows.drop 322)
    · exact right_parallel_002_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0334
  have h0310 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 107
      (PairLightPrepared14.rightCached.drop 310) (PairLightPrepared14.rightRows.drop 310) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 95
      (PairLightPrepared14.rightCached.drop 310) (PairLightPrepared14.rightRows.drop 310)
    · exact right_parallel_002_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0322
  have h0298 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 119
      (PairLightPrepared14.rightCached.drop 298) (PairLightPrepared14.rightRows.drop 298) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 107
      (PairLightPrepared14.rightCached.drop 298) (PairLightPrepared14.rightRows.drop 298)
    · exact right_parallel_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0310
  have h0286 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 131
      (PairLightPrepared14.rightCached.drop 286) (PairLightPrepared14.rightRows.drop 286) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 119
      (PairLightPrepared14.rightCached.drop 286) (PairLightPrepared14.rightRows.drop 286)
    · exact right_parallel_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0298
  have h0274 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 143
      (PairLightPrepared14.rightCached.drop 274) (PairLightPrepared14.rightRows.drop 274) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 131
      (PairLightPrepared14.rightCached.drop 274) (PairLightPrepared14.rightRows.drop 274)
    · exact right_parallel_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0286
  have h0262 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 155
      (PairLightPrepared14.rightCached.drop 262) (PairLightPrepared14.rightRows.drop 262) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 143
      (PairLightPrepared14.rightCached.drop 262) (PairLightPrepared14.rightRows.drop 262)
    · exact right_parallel_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0274
  have h0250 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 167
      (PairLightPrepared14.rightCached.drop 250) (PairLightPrepared14.rightRows.drop 250) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 155
      (PairLightPrepared14.rightCached.drop 250) (PairLightPrepared14.rightRows.drop 250)
    · exact right_parallel_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0262
  have h0238 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 179
      (PairLightPrepared14.rightCached.drop 238) (PairLightPrepared14.rightRows.drop 238) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 167
      (PairLightPrepared14.rightCached.drop 238) (PairLightPrepared14.rightRows.drop 238)
    · exact right_parallel_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0250
  have h0226 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 191
      (PairLightPrepared14.rightCached.drop 226) (PairLightPrepared14.rightRows.drop 226) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 179
      (PairLightPrepared14.rightCached.drop 226) (PairLightPrepared14.rightRows.drop 226)
    · exact right_parallel_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0238
  have h0214 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 203
      (PairLightPrepared14.rightCached.drop 214) (PairLightPrepared14.rightRows.drop 214) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 191
      (PairLightPrepared14.rightCached.drop 214) (PairLightPrepared14.rightRows.drop 214)
    · exact right_parallel_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0226
  have h0202 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 215
      (PairLightPrepared14.rightCached.drop 202) (PairLightPrepared14.rightRows.drop 202) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 203
      (PairLightPrepared14.rightCached.drop 202) (PairLightPrepared14.rightRows.drop 202)
    · exact right_parallel_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0214
  exact h0202

end D1Bound5.PairLightAdaptivePrepared14
end
