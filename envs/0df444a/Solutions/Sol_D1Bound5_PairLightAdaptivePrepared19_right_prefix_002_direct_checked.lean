-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_direct_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:31:01.531259+00:00
-- url     : https://prove2.me/submissions/4556d313-2736-4348-b284-ca3dd88b99b8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_prefix_002_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 198
      (PairLightPrepared19.rightCached.drop 248) (PairLightPrepared19.rightRows.drop 248) = true := by
  have h440 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 6
      (PairLightPrepared19.rightCached.drop 440) (PairLightPrepared19.rightRows.drop 440) = true := right_prefix_002_part08_checked
  have h416 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 30
      (PairLightPrepared19.rightCached.drop 416) (PairLightPrepared19.rightRows.drop 416) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 6
      (PairLightPrepared19.rightCached.drop 416) (PairLightPrepared19.rightRows.drop 416)
    · exact right_prefix_002_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h440
  have h392 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 54
      (PairLightPrepared19.rightCached.drop 392) (PairLightPrepared19.rightRows.drop 392) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 30
      (PairLightPrepared19.rightCached.drop 392) (PairLightPrepared19.rightRows.drop 392)
    · exact right_prefix_002_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h416
  have h368 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 78
      (PairLightPrepared19.rightCached.drop 368) (PairLightPrepared19.rightRows.drop 368) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 54
      (PairLightPrepared19.rightCached.drop 368) (PairLightPrepared19.rightRows.drop 368)
    · exact right_prefix_002_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h392
  have h344 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 102
      (PairLightPrepared19.rightCached.drop 344) (PairLightPrepared19.rightRows.drop 344) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 78
      (PairLightPrepared19.rightCached.drop 344) (PairLightPrepared19.rightRows.drop 344)
    · exact right_prefix_002_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h368
  have h320 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 126
      (PairLightPrepared19.rightCached.drop 320) (PairLightPrepared19.rightRows.drop 320) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 102
      (PairLightPrepared19.rightCached.drop 320) (PairLightPrepared19.rightRows.drop 320)
    · exact right_prefix_002_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h344
  have h296 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 150
      (PairLightPrepared19.rightCached.drop 296) (PairLightPrepared19.rightRows.drop 296) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 126
      (PairLightPrepared19.rightCached.drop 296) (PairLightPrepared19.rightRows.drop 296)
    · exact right_prefix_002_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h320
  have h272 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 174
      (PairLightPrepared19.rightCached.drop 272) (PairLightPrepared19.rightRows.drop 272) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 150
      (PairLightPrepared19.rightCached.drop 272) (PairLightPrepared19.rightRows.drop 272)
    · exact right_prefix_002_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h296
  have h248 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 198
      (PairLightPrepared19.rightCached.drop 248) (PairLightPrepared19.rightRows.drop 248) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared19.sieve 24 174
      (PairLightPrepared19.rightCached.drop 248) (PairLightPrepared19.rightRows.drop 248)
    · exact right_prefix_002_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h272
  exact h248
end D1Bound5.PairLightAdaptivePrepared19
end
