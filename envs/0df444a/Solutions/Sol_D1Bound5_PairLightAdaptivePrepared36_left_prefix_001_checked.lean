-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:31.855574+00:00
-- url     : https://prove2.me/submissions/06d1bda4-d4da-4ccb-b6a5-c615231ad007

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_001_part07_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 91
      leftCached001 leftRows001 = true := by
  have h0160 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 7
      (PairLightPrepared36.leftCached.drop 160) (PairLightPrepared36.leftRows.drop 160) = true := left_parallel_001_part07_checked
  have h0148 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 19
      (PairLightPrepared36.leftCached.drop 148) (PairLightPrepared36.leftRows.drop 148) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 7
      (PairLightPrepared36.leftCached.drop 148) (PairLightPrepared36.leftRows.drop 148)
    · exact left_parallel_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0160
  have h0136 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 31
      (PairLightPrepared36.leftCached.drop 136) (PairLightPrepared36.leftRows.drop 136) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 19
      (PairLightPrepared36.leftCached.drop 136) (PairLightPrepared36.leftRows.drop 136)
    · exact left_parallel_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0148
  have h0124 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 43
      (PairLightPrepared36.leftCached.drop 124) (PairLightPrepared36.leftRows.drop 124) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 31
      (PairLightPrepared36.leftCached.drop 124) (PairLightPrepared36.leftRows.drop 124)
    · exact left_parallel_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0136
  have h0112 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 55
      (PairLightPrepared36.leftCached.drop 112) (PairLightPrepared36.leftRows.drop 112) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 43
      (PairLightPrepared36.leftCached.drop 112) (PairLightPrepared36.leftRows.drop 112)
    · exact left_parallel_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0124
  have h0100 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 67
      (PairLightPrepared36.leftCached.drop 100) (PairLightPrepared36.leftRows.drop 100) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 55
      (PairLightPrepared36.leftCached.drop 100) (PairLightPrepared36.leftRows.drop 100)
    · exact left_parallel_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0112
  have h0088 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 79
      (PairLightPrepared36.leftCached.drop 88) (PairLightPrepared36.leftRows.drop 88) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 67
      (PairLightPrepared36.leftCached.drop 88) (PairLightPrepared36.leftRows.drop 88)
    · exact left_parallel_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0100
  have h0076 : pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 91
      (PairLightPrepared36.leftCached.drop 76) (PairLightPrepared36.leftRows.drop 76) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 2 PairLightPrepared36.sieve 12 79
      (PairLightPrepared36.leftCached.drop 76) (PairLightPrepared36.leftRows.drop 76)
    · exact left_parallel_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0088
  exact h0076

end D1Bound5.PairLightAdaptivePrepared36
end
