-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_prefix_003_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:13.509226+00:00
-- url     : https://prove2.me/submissions/75ac36bd-2eab-49fb-812d-cd0c4c9ccf32

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part15_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part16_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part17_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part18_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part19_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part20_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part21_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_parallel_003_part22_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 273
      rightCached003 rightRows003 = true := by
  have h0551 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 9
      (PairLightPrepared36.rightCached.drop 551) (PairLightPrepared36.rightRows.drop 551) = true := right_parallel_003_part22_checked
  have h0539 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 21
      (PairLightPrepared36.rightCached.drop 539) (PairLightPrepared36.rightRows.drop 539) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 9
      (PairLightPrepared36.rightCached.drop 539) (PairLightPrepared36.rightRows.drop 539)
    · exact right_parallel_003_part21_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0551
  have h0527 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 33
      (PairLightPrepared36.rightCached.drop 527) (PairLightPrepared36.rightRows.drop 527) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 21
      (PairLightPrepared36.rightCached.drop 527) (PairLightPrepared36.rightRows.drop 527)
    · exact right_parallel_003_part20_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0539
  have h0515 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 45
      (PairLightPrepared36.rightCached.drop 515) (PairLightPrepared36.rightRows.drop 515) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 33
      (PairLightPrepared36.rightCached.drop 515) (PairLightPrepared36.rightRows.drop 515)
    · exact right_parallel_003_part19_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0527
  have h0503 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 57
      (PairLightPrepared36.rightCached.drop 503) (PairLightPrepared36.rightRows.drop 503) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 45
      (PairLightPrepared36.rightCached.drop 503) (PairLightPrepared36.rightRows.drop 503)
    · exact right_parallel_003_part18_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0515
  have h0491 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 69
      (PairLightPrepared36.rightCached.drop 491) (PairLightPrepared36.rightRows.drop 491) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 57
      (PairLightPrepared36.rightCached.drop 491) (PairLightPrepared36.rightRows.drop 491)
    · exact right_parallel_003_part17_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0503
  have h0479 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 81
      (PairLightPrepared36.rightCached.drop 479) (PairLightPrepared36.rightRows.drop 479) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 69
      (PairLightPrepared36.rightCached.drop 479) (PairLightPrepared36.rightRows.drop 479)
    · exact right_parallel_003_part16_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0491
  have h0467 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 93
      (PairLightPrepared36.rightCached.drop 467) (PairLightPrepared36.rightRows.drop 467) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 81
      (PairLightPrepared36.rightCached.drop 467) (PairLightPrepared36.rightRows.drop 467)
    · exact right_parallel_003_part15_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0479
  have h0455 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 105
      (PairLightPrepared36.rightCached.drop 455) (PairLightPrepared36.rightRows.drop 455) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 93
      (PairLightPrepared36.rightCached.drop 455) (PairLightPrepared36.rightRows.drop 455)
    · exact right_parallel_003_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0467
  have h0443 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 117
      (PairLightPrepared36.rightCached.drop 443) (PairLightPrepared36.rightRows.drop 443) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 105
      (PairLightPrepared36.rightCached.drop 443) (PairLightPrepared36.rightRows.drop 443)
    · exact right_parallel_003_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0455
  have h0431 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 129
      (PairLightPrepared36.rightCached.drop 431) (PairLightPrepared36.rightRows.drop 431) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 117
      (PairLightPrepared36.rightCached.drop 431) (PairLightPrepared36.rightRows.drop 431)
    · exact right_parallel_003_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0443
  have h0419 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 141
      (PairLightPrepared36.rightCached.drop 419) (PairLightPrepared36.rightRows.drop 419) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 129
      (PairLightPrepared36.rightCached.drop 419) (PairLightPrepared36.rightRows.drop 419)
    · exact right_parallel_003_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0431
  have h0407 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 153
      (PairLightPrepared36.rightCached.drop 407) (PairLightPrepared36.rightRows.drop 407) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 141
      (PairLightPrepared36.rightCached.drop 407) (PairLightPrepared36.rightRows.drop 407)
    · exact right_parallel_003_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0419
  have h0395 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 165
      (PairLightPrepared36.rightCached.drop 395) (PairLightPrepared36.rightRows.drop 395) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 153
      (PairLightPrepared36.rightCached.drop 395) (PairLightPrepared36.rightRows.drop 395)
    · exact right_parallel_003_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0407
  have h0383 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 177
      (PairLightPrepared36.rightCached.drop 383) (PairLightPrepared36.rightRows.drop 383) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 165
      (PairLightPrepared36.rightCached.drop 383) (PairLightPrepared36.rightRows.drop 383)
    · exact right_parallel_003_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0395
  have h0371 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 189
      (PairLightPrepared36.rightCached.drop 371) (PairLightPrepared36.rightRows.drop 371) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 177
      (PairLightPrepared36.rightCached.drop 371) (PairLightPrepared36.rightRows.drop 371)
    · exact right_parallel_003_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0383
  have h0359 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 201
      (PairLightPrepared36.rightCached.drop 359) (PairLightPrepared36.rightRows.drop 359) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 189
      (PairLightPrepared36.rightCached.drop 359) (PairLightPrepared36.rightRows.drop 359)
    · exact right_parallel_003_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0371
  have h0347 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 213
      (PairLightPrepared36.rightCached.drop 347) (PairLightPrepared36.rightRows.drop 347) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 201
      (PairLightPrepared36.rightCached.drop 347) (PairLightPrepared36.rightRows.drop 347)
    · exact right_parallel_003_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0359
  have h0335 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 225
      (PairLightPrepared36.rightCached.drop 335) (PairLightPrepared36.rightRows.drop 335) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 213
      (PairLightPrepared36.rightCached.drop 335) (PairLightPrepared36.rightRows.drop 335)
    · exact right_parallel_003_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0347
  have h0323 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 237
      (PairLightPrepared36.rightCached.drop 323) (PairLightPrepared36.rightRows.drop 323) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 225
      (PairLightPrepared36.rightCached.drop 323) (PairLightPrepared36.rightRows.drop 323)
    · exact right_parallel_003_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0335
  have h0311 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 249
      (PairLightPrepared36.rightCached.drop 311) (PairLightPrepared36.rightRows.drop 311) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 237
      (PairLightPrepared36.rightCached.drop 311) (PairLightPrepared36.rightRows.drop 311)
    · exact right_parallel_003_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0323
  have h0299 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 261
      (PairLightPrepared36.rightCached.drop 299) (PairLightPrepared36.rightRows.drop 299) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 249
      (PairLightPrepared36.rightCached.drop 299) (PairLightPrepared36.rightRows.drop 299)
    · exact right_parallel_003_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0311
  have h0287 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 273
      (PairLightPrepared36.rightCached.drop 287) (PairLightPrepared36.rightRows.drop 287) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 261
      (PairLightPrepared36.rightCached.drop 287) (PairLightPrepared36.rightRows.drop 287)
    · exact right_parallel_003_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0299
  exact h0287

end D1Bound5.PairLightAdaptivePrepared36
end
