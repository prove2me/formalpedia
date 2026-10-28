-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_prefix_003_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:22:08.729993+00:00
-- url     : https://prove2.me/submissions/74d1cdb8-538e-4bbe-9325-0ec0c947362e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part10_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part11_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part12_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part13_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part14_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part15_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 189
      rightCached003 rightRows003 = true := by
  have h0515 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 9
      (PairLightPrepared28.rightCached.drop 515) (PairLightPrepared28.rightRows.drop 515) = true := right_parallel_003_part15_checked
  have h0503 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 21
      (PairLightPrepared28.rightCached.drop 503) (PairLightPrepared28.rightRows.drop 503) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 9
      (PairLightPrepared28.rightCached.drop 503) (PairLightPrepared28.rightRows.drop 503)
    · exact right_parallel_003_part14_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0515
  have h0491 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 33
      (PairLightPrepared28.rightCached.drop 491) (PairLightPrepared28.rightRows.drop 491) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 21
      (PairLightPrepared28.rightCached.drop 491) (PairLightPrepared28.rightRows.drop 491)
    · exact right_parallel_003_part13_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0503
  have h0479 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 45
      (PairLightPrepared28.rightCached.drop 479) (PairLightPrepared28.rightRows.drop 479) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 33
      (PairLightPrepared28.rightCached.drop 479) (PairLightPrepared28.rightRows.drop 479)
    · exact right_parallel_003_part12_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0491
  have h0467 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 57
      (PairLightPrepared28.rightCached.drop 467) (PairLightPrepared28.rightRows.drop 467) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 45
      (PairLightPrepared28.rightCached.drop 467) (PairLightPrepared28.rightRows.drop 467)
    · exact right_parallel_003_part11_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0479
  have h0455 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 69
      (PairLightPrepared28.rightCached.drop 455) (PairLightPrepared28.rightRows.drop 455) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 57
      (PairLightPrepared28.rightCached.drop 455) (PairLightPrepared28.rightRows.drop 455)
    · exact right_parallel_003_part10_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0467
  have h0443 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 81
      (PairLightPrepared28.rightCached.drop 443) (PairLightPrepared28.rightRows.drop 443) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 69
      (PairLightPrepared28.rightCached.drop 443) (PairLightPrepared28.rightRows.drop 443)
    · exact right_parallel_003_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0455
  have h0431 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 93
      (PairLightPrepared28.rightCached.drop 431) (PairLightPrepared28.rightRows.drop 431) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 81
      (PairLightPrepared28.rightCached.drop 431) (PairLightPrepared28.rightRows.drop 431)
    · exact right_parallel_003_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0443
  have h0419 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 105
      (PairLightPrepared28.rightCached.drop 419) (PairLightPrepared28.rightRows.drop 419) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 93
      (PairLightPrepared28.rightCached.drop 419) (PairLightPrepared28.rightRows.drop 419)
    · exact right_parallel_003_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0431
  have h0407 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 117
      (PairLightPrepared28.rightCached.drop 407) (PairLightPrepared28.rightRows.drop 407) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 105
      (PairLightPrepared28.rightCached.drop 407) (PairLightPrepared28.rightRows.drop 407)
    · exact right_parallel_003_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0419
  have h0395 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 129
      (PairLightPrepared28.rightCached.drop 395) (PairLightPrepared28.rightRows.drop 395) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 117
      (PairLightPrepared28.rightCached.drop 395) (PairLightPrepared28.rightRows.drop 395)
    · exact right_parallel_003_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0407
  have h0383 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 141
      (PairLightPrepared28.rightCached.drop 383) (PairLightPrepared28.rightRows.drop 383) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 129
      (PairLightPrepared28.rightCached.drop 383) (PairLightPrepared28.rightRows.drop 383)
    · exact right_parallel_003_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0395
  have h0371 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 153
      (PairLightPrepared28.rightCached.drop 371) (PairLightPrepared28.rightRows.drop 371) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 141
      (PairLightPrepared28.rightCached.drop 371) (PairLightPrepared28.rightRows.drop 371)
    · exact right_parallel_003_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0383
  have h0359 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 165
      (PairLightPrepared28.rightCached.drop 359) (PairLightPrepared28.rightRows.drop 359) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 153
      (PairLightPrepared28.rightCached.drop 359) (PairLightPrepared28.rightRows.drop 359)
    · exact right_parallel_003_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0371
  have h0347 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 177
      (PairLightPrepared28.rightCached.drop 347) (PairLightPrepared28.rightRows.drop 347) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 165
      (PairLightPrepared28.rightCached.drop 347) (PairLightPrepared28.rightRows.drop 347)
    · exact right_parallel_003_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0359
  have h0335 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 189
      (PairLightPrepared28.rightCached.drop 335) (PairLightPrepared28.rightRows.drop 335) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 177
      (PairLightPrepared28.rightCached.drop 335) (PairLightPrepared28.rightRows.drop 335)
    · exact right_parallel_003_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0347
  exact h0335

end D1Bound5.PairLightAdaptivePrepared28
end
