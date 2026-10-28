-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_prefix_002_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:30:54.512685+00:00
-- url     : https://prove2.me/submissions/2900d6b4-18f0-4e82-9677-a4721ae56274

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part18_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part19_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part20_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part21_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_002_part22_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 270
      leftCached002 leftRows002 = true := by
  have h0476 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 6
      (PairLightPrepared23.leftCached.drop 476) (PairLightPrepared23.leftRows.drop 476) = true := left_parallel_002_part22_checked
  have h0464 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 18
      (PairLightPrepared23.leftCached.drop 464) (PairLightPrepared23.leftRows.drop 464) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 6
      (PairLightPrepared23.leftCached.drop 464) (PairLightPrepared23.leftRows.drop 464)
    · exact left_parallel_002_part21_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0476
  have h0452 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 30
      (PairLightPrepared23.leftCached.drop 452) (PairLightPrepared23.leftRows.drop 452) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 18
      (PairLightPrepared23.leftCached.drop 452) (PairLightPrepared23.leftRows.drop 452)
    · exact left_parallel_002_part20_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0464
  have h0440 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 42
      (PairLightPrepared23.leftCached.drop 440) (PairLightPrepared23.leftRows.drop 440) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 30
      (PairLightPrepared23.leftCached.drop 440) (PairLightPrepared23.leftRows.drop 440)
    · exact left_parallel_002_part19_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0452
  have h0428 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 54
      (PairLightPrepared23.leftCached.drop 428) (PairLightPrepared23.leftRows.drop 428) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 42
      (PairLightPrepared23.leftCached.drop 428) (PairLightPrepared23.leftRows.drop 428)
    · exact left_parallel_002_part18_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0440
  have h0416 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 66
      (PairLightPrepared23.leftCached.drop 416) (PairLightPrepared23.leftRows.drop 416) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 54
      (PairLightPrepared23.leftCached.drop 416) (PairLightPrepared23.leftRows.drop 416)
    · exact left_parallel_002_part17_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0428
  have h0404 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 78
      (PairLightPrepared23.leftCached.drop 404) (PairLightPrepared23.leftRows.drop 404) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 66
      (PairLightPrepared23.leftCached.drop 404) (PairLightPrepared23.leftRows.drop 404)
    · exact left_parallel_002_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0416
  have h0392 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 90
      (PairLightPrepared23.leftCached.drop 392) (PairLightPrepared23.leftRows.drop 392) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 78
      (PairLightPrepared23.leftCached.drop 392) (PairLightPrepared23.leftRows.drop 392)
    · exact left_parallel_002_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0404
  have h0380 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 102
      (PairLightPrepared23.leftCached.drop 380) (PairLightPrepared23.leftRows.drop 380) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 90
      (PairLightPrepared23.leftCached.drop 380) (PairLightPrepared23.leftRows.drop 380)
    · exact left_parallel_002_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0392
  have h0368 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 114
      (PairLightPrepared23.leftCached.drop 368) (PairLightPrepared23.leftRows.drop 368) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 102
      (PairLightPrepared23.leftCached.drop 368) (PairLightPrepared23.leftRows.drop 368)
    · exact left_parallel_002_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0380
  have h0356 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 126
      (PairLightPrepared23.leftCached.drop 356) (PairLightPrepared23.leftRows.drop 356) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 114
      (PairLightPrepared23.leftCached.drop 356) (PairLightPrepared23.leftRows.drop 356)
    · exact left_parallel_002_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0368
  have h0344 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 138
      (PairLightPrepared23.leftCached.drop 344) (PairLightPrepared23.leftRows.drop 344) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 126
      (PairLightPrepared23.leftCached.drop 344) (PairLightPrepared23.leftRows.drop 344)
    · exact left_parallel_002_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0356
  have h0332 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 150
      (PairLightPrepared23.leftCached.drop 332) (PairLightPrepared23.leftRows.drop 332) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 138
      (PairLightPrepared23.leftCached.drop 332) (PairLightPrepared23.leftRows.drop 332)
    · exact left_parallel_002_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0344
  have h0320 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 162
      (PairLightPrepared23.leftCached.drop 320) (PairLightPrepared23.leftRows.drop 320) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 150
      (PairLightPrepared23.leftCached.drop 320) (PairLightPrepared23.leftRows.drop 320)
    · exact left_parallel_002_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0332
  have h0308 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 174
      (PairLightPrepared23.leftCached.drop 308) (PairLightPrepared23.leftRows.drop 308) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 162
      (PairLightPrepared23.leftCached.drop 308) (PairLightPrepared23.leftRows.drop 308)
    · exact left_parallel_002_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0320
  have h0296 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 186
      (PairLightPrepared23.leftCached.drop 296) (PairLightPrepared23.leftRows.drop 296) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 174
      (PairLightPrepared23.leftCached.drop 296) (PairLightPrepared23.leftRows.drop 296)
    · exact left_parallel_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0308
  have h0284 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 198
      (PairLightPrepared23.leftCached.drop 284) (PairLightPrepared23.leftRows.drop 284) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 186
      (PairLightPrepared23.leftCached.drop 284) (PairLightPrepared23.leftRows.drop 284)
    · exact left_parallel_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0296
  have h0272 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 210
      (PairLightPrepared23.leftCached.drop 272) (PairLightPrepared23.leftRows.drop 272) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 198
      (PairLightPrepared23.leftCached.drop 272) (PairLightPrepared23.leftRows.drop 272)
    · exact left_parallel_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0284
  have h0260 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 222
      (PairLightPrepared23.leftCached.drop 260) (PairLightPrepared23.leftRows.drop 260) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 210
      (PairLightPrepared23.leftCached.drop 260) (PairLightPrepared23.leftRows.drop 260)
    · exact left_parallel_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0272
  have h0248 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 234
      (PairLightPrepared23.leftCached.drop 248) (PairLightPrepared23.leftRows.drop 248) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 222
      (PairLightPrepared23.leftCached.drop 248) (PairLightPrepared23.leftRows.drop 248)
    · exact left_parallel_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0260
  have h0236 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 246
      (PairLightPrepared23.leftCached.drop 236) (PairLightPrepared23.leftRows.drop 236) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 234
      (PairLightPrepared23.leftCached.drop 236) (PairLightPrepared23.leftRows.drop 236)
    · exact left_parallel_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0248
  have h0224 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 258
      (PairLightPrepared23.leftCached.drop 224) (PairLightPrepared23.leftRows.drop 224) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 246
      (PairLightPrepared23.leftCached.drop 224) (PairLightPrepared23.leftRows.drop 224)
    · exact left_parallel_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0236
  have h0212 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 270
      (PairLightPrepared23.leftCached.drop 212) (PairLightPrepared23.leftRows.drop 212) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 258
      (PairLightPrepared23.leftCached.drop 212) (PairLightPrepared23.leftRows.drop 212)
    · exact left_parallel_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0224
  exact h0212

end D1Bound5.PairLightAdaptivePrepared23
end
