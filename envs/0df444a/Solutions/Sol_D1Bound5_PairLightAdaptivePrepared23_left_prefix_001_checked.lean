-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:14.068324+00:00
-- url     : https://prove2.me/submissions/d7cda946-9827-4b6f-a8cf-23163d92e165

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part07_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part08_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part09_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_001_part10_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 121
      leftCached001 leftRows001 = true := by
  have h0211 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 1
      (PairLightPrepared23.leftCached.drop 211) (PairLightPrepared23.leftRows.drop 211) = true := left_parallel_001_part10_checked
  have h0199 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 13
      (PairLightPrepared23.leftCached.drop 199) (PairLightPrepared23.leftRows.drop 199) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 1
      (PairLightPrepared23.leftCached.drop 199) (PairLightPrepared23.leftRows.drop 199)
    · exact left_parallel_001_part09_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0211
  have h0187 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 25
      (PairLightPrepared23.leftCached.drop 187) (PairLightPrepared23.leftRows.drop 187) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 13
      (PairLightPrepared23.leftCached.drop 187) (PairLightPrepared23.leftRows.drop 187)
    · exact left_parallel_001_part08_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0199
  have h0175 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 37
      (PairLightPrepared23.leftCached.drop 175) (PairLightPrepared23.leftRows.drop 175) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 25
      (PairLightPrepared23.leftCached.drop 175) (PairLightPrepared23.leftRows.drop 175)
    · exact left_parallel_001_part07_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0187
  have h0163 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 49
      (PairLightPrepared23.leftCached.drop 163) (PairLightPrepared23.leftRows.drop 163) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 37
      (PairLightPrepared23.leftCached.drop 163) (PairLightPrepared23.leftRows.drop 163)
    · exact left_parallel_001_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0175
  have h0151 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 61
      (PairLightPrepared23.leftCached.drop 151) (PairLightPrepared23.leftRows.drop 151) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 49
      (PairLightPrepared23.leftCached.drop 151) (PairLightPrepared23.leftRows.drop 151)
    · exact left_parallel_001_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0163
  have h0139 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 73
      (PairLightPrepared23.leftCached.drop 139) (PairLightPrepared23.leftRows.drop 139) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 61
      (PairLightPrepared23.leftCached.drop 139) (PairLightPrepared23.leftRows.drop 139)
    · exact left_parallel_001_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0151
  have h0127 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 85
      (PairLightPrepared23.leftCached.drop 127) (PairLightPrepared23.leftRows.drop 127) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 73
      (PairLightPrepared23.leftCached.drop 127) (PairLightPrepared23.leftRows.drop 127)
    · exact left_parallel_001_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0139
  have h0115 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 97
      (PairLightPrepared23.leftCached.drop 115) (PairLightPrepared23.leftRows.drop 115) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 85
      (PairLightPrepared23.leftCached.drop 115) (PairLightPrepared23.leftRows.drop 115)
    · exact left_parallel_001_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0127
  have h0103 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 109
      (PairLightPrepared23.leftCached.drop 103) (PairLightPrepared23.leftRows.drop 103) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 97
      (PairLightPrepared23.leftCached.drop 103) (PairLightPrepared23.leftRows.drop 103)
    · exact left_parallel_001_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0115
  have h0091 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 121
      (PairLightPrepared23.leftCached.drop 91) (PairLightPrepared23.leftRows.drop 91) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 109
      (PairLightPrepared23.leftCached.drop 91) (PairLightPrepared23.leftRows.drop 91)
    · exact left_parallel_001_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0103
  exact h0091

end D1Bound5.PairLightAdaptivePrepared23
end
