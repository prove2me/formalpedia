-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:34:35.977993+00:00
-- url     : https://prove2.me/submissions/1aaeab88-fad1-4487-8730-6b0f8664707f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part08_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 102
      leftCached001 leftRows001 = true := by
  have h0178 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 6
      (PairLightPrepared21.leftCached.drop 178) (PairLightPrepared21.leftRows.drop 178) = true := left_parallel_001_part08_checked
  have h0166 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 18
      (PairLightPrepared21.leftCached.drop 166) (PairLightPrepared21.leftRows.drop 166) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 6
      (PairLightPrepared21.leftCached.drop 166) (PairLightPrepared21.leftRows.drop 166)
    · exact left_parallel_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0178
  have h0154 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 30
      (PairLightPrepared21.leftCached.drop 154) (PairLightPrepared21.leftRows.drop 154) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 18
      (PairLightPrepared21.leftCached.drop 154) (PairLightPrepared21.leftRows.drop 154)
    · exact left_parallel_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0166
  have h0142 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 42
      (PairLightPrepared21.leftCached.drop 142) (PairLightPrepared21.leftRows.drop 142) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 30
      (PairLightPrepared21.leftCached.drop 142) (PairLightPrepared21.leftRows.drop 142)
    · exact left_parallel_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0154
  have h0130 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 54
      (PairLightPrepared21.leftCached.drop 130) (PairLightPrepared21.leftRows.drop 130) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 42
      (PairLightPrepared21.leftCached.drop 130) (PairLightPrepared21.leftRows.drop 130)
    · exact left_parallel_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0142
  have h0118 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 66
      (PairLightPrepared21.leftCached.drop 118) (PairLightPrepared21.leftRows.drop 118) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 54
      (PairLightPrepared21.leftCached.drop 118) (PairLightPrepared21.leftRows.drop 118)
    · exact left_parallel_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0130
  have h0106 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 78
      (PairLightPrepared21.leftCached.drop 106) (PairLightPrepared21.leftRows.drop 106) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 66
      (PairLightPrepared21.leftCached.drop 106) (PairLightPrepared21.leftRows.drop 106)
    · exact left_parallel_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0118
  have h0094 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 90
      (PairLightPrepared21.leftCached.drop 94) (PairLightPrepared21.leftRows.drop 94) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 78
      (PairLightPrepared21.leftCached.drop 94) (PairLightPrepared21.leftRows.drop 94)
    · exact left_parallel_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0106
  have h0082 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 102
      (PairLightPrepared21.leftCached.drop 82) (PairLightPrepared21.leftRows.drop 82) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared21.sieve 12 90
      (PairLightPrepared21.leftCached.drop 82) (PairLightPrepared21.leftRows.drop 82)
    · exact left_parallel_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0094
  exact h0082

end D1Bound5.PairLightAdaptivePrepared21
end
