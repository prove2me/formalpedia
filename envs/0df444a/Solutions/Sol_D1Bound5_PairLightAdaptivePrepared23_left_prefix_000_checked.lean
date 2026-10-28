-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:22:07.916898+00:00
-- url     : https://prove2.me/submissions/dcf9b886-0da8-46a2-9a70-26329cf4d6eb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part06_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_parallel_000_part07_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 91
      leftCached000 leftRows000 = true := by
  have h0084 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 7
      (PairLightPrepared23.leftCached.drop 84) (PairLightPrepared23.leftRows.drop 84) = true := left_parallel_000_part07_checked
  have h0072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 19
      (PairLightPrepared23.leftCached.drop 72) (PairLightPrepared23.leftRows.drop 72) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 7
      (PairLightPrepared23.leftCached.drop 72) (PairLightPrepared23.leftRows.drop 72)
    · exact left_parallel_000_part06_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0084
  have h0060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 31
      (PairLightPrepared23.leftCached.drop 60) (PairLightPrepared23.leftRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 19
      (PairLightPrepared23.leftCached.drop 60) (PairLightPrepared23.leftRows.drop 60)
    · exact left_parallel_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0072
  have h0048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 43
      (PairLightPrepared23.leftCached.drop 48) (PairLightPrepared23.leftRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 31
      (PairLightPrepared23.leftCached.drop 48) (PairLightPrepared23.leftRows.drop 48)
    · exact left_parallel_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0060
  have h0036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 55
      (PairLightPrepared23.leftCached.drop 36) (PairLightPrepared23.leftRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 43
      (PairLightPrepared23.leftCached.drop 36) (PairLightPrepared23.leftRows.drop 36)
    · exact left_parallel_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0048
  have h0024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 67
      (PairLightPrepared23.leftCached.drop 24) (PairLightPrepared23.leftRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 55
      (PairLightPrepared23.leftCached.drop 24) (PairLightPrepared23.leftRows.drop 24)
    · exact left_parallel_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0036
  have h0012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 79
      (PairLightPrepared23.leftCached.drop 12) (PairLightPrepared23.leftRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 67
      (PairLightPrepared23.leftCached.drop 12) (PairLightPrepared23.leftRows.drop 12)
    · exact left_parallel_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0024
  have h0000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 91
      (PairLightPrepared23.leftCached.drop 0) (PairLightPrepared23.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared23.sieve 12 79
      (PairLightPrepared23.leftCached.drop 0) (PairLightPrepared23.leftRows.drop 0)
    · exact left_parallel_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0012
  exact h0000

end D1Bound5.PairLightAdaptivePrepared23
end
