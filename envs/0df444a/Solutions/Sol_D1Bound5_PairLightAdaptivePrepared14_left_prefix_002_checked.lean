-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:29.855991+00:00
-- url     : https://prove2.me/submissions/bb54cbde-dbf1-4a79-9712-4f6c254f7f88

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_parallel_002_part18_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 217
      leftCached002 leftRows002 = true := by
  have h0418 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 1
      (PairLightPrepared14.leftCached.drop 418) (PairLightPrepared14.leftRows.drop 418) = true := left_parallel_002_part18_checked
  have h0406 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 13
      (PairLightPrepared14.leftCached.drop 406) (PairLightPrepared14.leftRows.drop 406) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 1
      (PairLightPrepared14.leftCached.drop 406) (PairLightPrepared14.leftRows.drop 406)
    · exact left_parallel_002_part17_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0418
  have h0394 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 25
      (PairLightPrepared14.leftCached.drop 394) (PairLightPrepared14.leftRows.drop 394) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 13
      (PairLightPrepared14.leftCached.drop 394) (PairLightPrepared14.leftRows.drop 394)
    · exact left_parallel_002_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0406
  have h0382 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 37
      (PairLightPrepared14.leftCached.drop 382) (PairLightPrepared14.leftRows.drop 382) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 25
      (PairLightPrepared14.leftCached.drop 382) (PairLightPrepared14.leftRows.drop 382)
    · exact left_parallel_002_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0394
  have h0370 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 49
      (PairLightPrepared14.leftCached.drop 370) (PairLightPrepared14.leftRows.drop 370) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 37
      (PairLightPrepared14.leftCached.drop 370) (PairLightPrepared14.leftRows.drop 370)
    · exact left_parallel_002_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0382
  have h0358 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 61
      (PairLightPrepared14.leftCached.drop 358) (PairLightPrepared14.leftRows.drop 358) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 49
      (PairLightPrepared14.leftCached.drop 358) (PairLightPrepared14.leftRows.drop 358)
    · exact left_parallel_002_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0370
  have h0346 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 73
      (PairLightPrepared14.leftCached.drop 346) (PairLightPrepared14.leftRows.drop 346) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 61
      (PairLightPrepared14.leftCached.drop 346) (PairLightPrepared14.leftRows.drop 346)
    · exact left_parallel_002_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0358
  have h0334 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 85
      (PairLightPrepared14.leftCached.drop 334) (PairLightPrepared14.leftRows.drop 334) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 73
      (PairLightPrepared14.leftCached.drop 334) (PairLightPrepared14.leftRows.drop 334)
    · exact left_parallel_002_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0346
  have h0322 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 97
      (PairLightPrepared14.leftCached.drop 322) (PairLightPrepared14.leftRows.drop 322) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 85
      (PairLightPrepared14.leftCached.drop 322) (PairLightPrepared14.leftRows.drop 322)
    · exact left_parallel_002_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0334
  have h0310 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 109
      (PairLightPrepared14.leftCached.drop 310) (PairLightPrepared14.leftRows.drop 310) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 97
      (PairLightPrepared14.leftCached.drop 310) (PairLightPrepared14.leftRows.drop 310)
    · exact left_parallel_002_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0322
  have h0298 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 121
      (PairLightPrepared14.leftCached.drop 298) (PairLightPrepared14.leftRows.drop 298) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 109
      (PairLightPrepared14.leftCached.drop 298) (PairLightPrepared14.leftRows.drop 298)
    · exact left_parallel_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0310
  have h0286 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 133
      (PairLightPrepared14.leftCached.drop 286) (PairLightPrepared14.leftRows.drop 286) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 121
      (PairLightPrepared14.leftCached.drop 286) (PairLightPrepared14.leftRows.drop 286)
    · exact left_parallel_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0298
  have h0274 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 145
      (PairLightPrepared14.leftCached.drop 274) (PairLightPrepared14.leftRows.drop 274) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 133
      (PairLightPrepared14.leftCached.drop 274) (PairLightPrepared14.leftRows.drop 274)
    · exact left_parallel_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0286
  have h0262 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 157
      (PairLightPrepared14.leftCached.drop 262) (PairLightPrepared14.leftRows.drop 262) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 145
      (PairLightPrepared14.leftCached.drop 262) (PairLightPrepared14.leftRows.drop 262)
    · exact left_parallel_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0274
  have h0250 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 169
      (PairLightPrepared14.leftCached.drop 250) (PairLightPrepared14.leftRows.drop 250) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 157
      (PairLightPrepared14.leftCached.drop 250) (PairLightPrepared14.leftRows.drop 250)
    · exact left_parallel_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0262
  have h0238 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 181
      (PairLightPrepared14.leftCached.drop 238) (PairLightPrepared14.leftRows.drop 238) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 169
      (PairLightPrepared14.leftCached.drop 238) (PairLightPrepared14.leftRows.drop 238)
    · exact left_parallel_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0250
  have h0226 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 193
      (PairLightPrepared14.leftCached.drop 226) (PairLightPrepared14.leftRows.drop 226) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 181
      (PairLightPrepared14.leftCached.drop 226) (PairLightPrepared14.leftRows.drop 226)
    · exact left_parallel_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0238
  have h0214 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 205
      (PairLightPrepared14.leftCached.drop 214) (PairLightPrepared14.leftRows.drop 214) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 193
      (PairLightPrepared14.leftCached.drop 214) (PairLightPrepared14.leftRows.drop 214)
    · exact left_parallel_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0226
  have h0202 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 217
      (PairLightPrepared14.leftCached.drop 202) (PairLightPrepared14.leftRows.drop 202) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 205
      (PairLightPrepared14.leftCached.drop 202) (PairLightPrepared14.leftRows.drop 202)
    · exact left_parallel_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0214
  exact h0202

end D1Bound5.PairLightAdaptivePrepared14
end
