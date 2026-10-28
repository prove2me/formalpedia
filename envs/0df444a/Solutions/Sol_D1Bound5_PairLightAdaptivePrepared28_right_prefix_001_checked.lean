-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:33:29.210652+00:00
-- url     : https://prove2.me/submissions/bc88ee9b-f26d-4fe8-9c13-6c64e95e0742

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 102
      rightCached001 rightRows001 = true := by
  have h0178 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 6
      (PairLightPrepared28.rightCached.drop 178) (PairLightPrepared28.rightRows.drop 178) = true := right_parallel_001_part08_checked
  have h0166 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 18
      (PairLightPrepared28.rightCached.drop 166) (PairLightPrepared28.rightRows.drop 166) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 6
      (PairLightPrepared28.rightCached.drop 166) (PairLightPrepared28.rightRows.drop 166)
    · exact right_parallel_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0178
  have h0154 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 30
      (PairLightPrepared28.rightCached.drop 154) (PairLightPrepared28.rightRows.drop 154) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 18
      (PairLightPrepared28.rightCached.drop 154) (PairLightPrepared28.rightRows.drop 154)
    · exact right_parallel_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0166
  have h0142 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 42
      (PairLightPrepared28.rightCached.drop 142) (PairLightPrepared28.rightRows.drop 142) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 30
      (PairLightPrepared28.rightCached.drop 142) (PairLightPrepared28.rightRows.drop 142)
    · exact right_parallel_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0154
  have h0130 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 54
      (PairLightPrepared28.rightCached.drop 130) (PairLightPrepared28.rightRows.drop 130) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 42
      (PairLightPrepared28.rightCached.drop 130) (PairLightPrepared28.rightRows.drop 130)
    · exact right_parallel_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0142
  have h0118 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 66
      (PairLightPrepared28.rightCached.drop 118) (PairLightPrepared28.rightRows.drop 118) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 54
      (PairLightPrepared28.rightCached.drop 118) (PairLightPrepared28.rightRows.drop 118)
    · exact right_parallel_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0130
  have h0106 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 78
      (PairLightPrepared28.rightCached.drop 106) (PairLightPrepared28.rightRows.drop 106) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 66
      (PairLightPrepared28.rightCached.drop 106) (PairLightPrepared28.rightRows.drop 106)
    · exact right_parallel_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0118
  have h0094 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 90
      (PairLightPrepared28.rightCached.drop 94) (PairLightPrepared28.rightRows.drop 94) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 78
      (PairLightPrepared28.rightCached.drop 94) (PairLightPrepared28.rightRows.drop 94)
    · exact right_parallel_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0106
  have h0082 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 102
      (PairLightPrepared28.rightCached.drop 82) (PairLightPrepared28.rightRows.drop 82) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 90
      (PairLightPrepared28.rightCached.drop 82) (PairLightPrepared28.rightRows.drop 82)
    · exact right_parallel_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0094
  exact h0082

end D1Bound5.PairLightAdaptivePrepared28
end
