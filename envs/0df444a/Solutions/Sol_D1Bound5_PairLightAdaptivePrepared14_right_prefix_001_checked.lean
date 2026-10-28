-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:31.702412+00:00
-- url     : https://prove2.me/submissions/ccde7fc3-08df-4c79-9e3e-48a1e7d242f5

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_001_part09_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 114
      rightCached001 rightRows001 = true := by
  have h0196 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 6
      (PairLightPrepared14.rightCached.drop 196) (PairLightPrepared14.rightRows.drop 196) = true := right_parallel_001_part09_checked
  have h0184 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 18
      (PairLightPrepared14.rightCached.drop 184) (PairLightPrepared14.rightRows.drop 184) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 6
      (PairLightPrepared14.rightCached.drop 184) (PairLightPrepared14.rightRows.drop 184)
    · exact right_parallel_001_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0196
  have h0172 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 30
      (PairLightPrepared14.rightCached.drop 172) (PairLightPrepared14.rightRows.drop 172) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 18
      (PairLightPrepared14.rightCached.drop 172) (PairLightPrepared14.rightRows.drop 172)
    · exact right_parallel_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0184
  have h0160 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 42
      (PairLightPrepared14.rightCached.drop 160) (PairLightPrepared14.rightRows.drop 160) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 30
      (PairLightPrepared14.rightCached.drop 160) (PairLightPrepared14.rightRows.drop 160)
    · exact right_parallel_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0172
  have h0148 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 54
      (PairLightPrepared14.rightCached.drop 148) (PairLightPrepared14.rightRows.drop 148) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 42
      (PairLightPrepared14.rightCached.drop 148) (PairLightPrepared14.rightRows.drop 148)
    · exact right_parallel_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0160
  have h0136 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 66
      (PairLightPrepared14.rightCached.drop 136) (PairLightPrepared14.rightRows.drop 136) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 54
      (PairLightPrepared14.rightCached.drop 136) (PairLightPrepared14.rightRows.drop 136)
    · exact right_parallel_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0148
  have h0124 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 78
      (PairLightPrepared14.rightCached.drop 124) (PairLightPrepared14.rightRows.drop 124) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 66
      (PairLightPrepared14.rightCached.drop 124) (PairLightPrepared14.rightRows.drop 124)
    · exact right_parallel_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0136
  have h0112 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 90
      (PairLightPrepared14.rightCached.drop 112) (PairLightPrepared14.rightRows.drop 112) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 78
      (PairLightPrepared14.rightCached.drop 112) (PairLightPrepared14.rightRows.drop 112)
    · exact right_parallel_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0124
  have h0100 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 102
      (PairLightPrepared14.rightCached.drop 100) (PairLightPrepared14.rightRows.drop 100) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 90
      (PairLightPrepared14.rightCached.drop 100) (PairLightPrepared14.rightRows.drop 100)
    · exact right_parallel_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0112
  have h0088 : pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 114
      (PairLightPrepared14.rightCached.drop 88) (PairLightPrepared14.rightRows.drop 88) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 0 2 PairLightPrepared14.sieve 12 102
      (PairLightPrepared14.rightCached.drop 88) (PairLightPrepared14.rightRows.drop 88)
    · exact right_parallel_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0100
  exact h0088

end D1Bound5.PairLightAdaptivePrepared14
end
