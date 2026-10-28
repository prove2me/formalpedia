-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:22.553901+00:00
-- url     : https://prove2.me/submissions/71ea8c40-2450-476b-9af4-9aec574fc499

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData28_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part00_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part01_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part02_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part03_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part04_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part05_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part06_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorPrefixBool_of_add

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 82
      leftCached000 leftRows000 = true := by
  have h0072 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 10
      (PairLightPrepared28.leftCached.drop 72) (PairLightPrepared28.leftRows.drop 72) = true := left_parallel_000_part06_checked
  have h0060 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 22
      (PairLightPrepared28.leftCached.drop 60) (PairLightPrepared28.leftRows.drop 60) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 10
      (PairLightPrepared28.leftCached.drop 60) (PairLightPrepared28.leftRows.drop 60)
    · exact left_parallel_000_part05_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0072
  have h0048 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 34
      (PairLightPrepared28.leftCached.drop 48) (PairLightPrepared28.leftRows.drop 48) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 22
      (PairLightPrepared28.leftCached.drop 48) (PairLightPrepared28.leftRows.drop 48)
    · exact left_parallel_000_part04_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0060
  have h0036 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 46
      (PairLightPrepared28.leftCached.drop 36) (PairLightPrepared28.leftRows.drop 36) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 34
      (PairLightPrepared28.leftCached.drop 36) (PairLightPrepared28.leftRows.drop 36)
    · exact left_parallel_000_part03_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0048
  have h0024 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 58
      (PairLightPrepared28.leftCached.drop 24) (PairLightPrepared28.leftRows.drop 24) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 46
      (PairLightPrepared28.leftCached.drop 24) (PairLightPrepared28.leftRows.drop 24)
    · exact left_parallel_000_part02_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0036
  have h0012 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 70
      (PairLightPrepared28.leftCached.drop 12) (PairLightPrepared28.leftRows.drop 12) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 58
      (PairLightPrepared28.leftCached.drop 12) (PairLightPrepared28.leftRows.drop 12)
    · exact left_parallel_000_part01_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0024
  have h0000 : pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 82
      (PairLightPrepared28.leftCached.drop 0) (PairLightPrepared28.leftRows.drop 0) = true := by
    apply pairLightSelectedFloorPrefixBool_of_add 1 1 PairLightPrepared28.sieve 12 70
      (PairLightPrepared28.leftCached.drop 0) (PairLightPrepared28.leftRows.drop 0)
    · exact left_parallel_000_part00_checked
    · simpa only [List.drop_drop, Nat.reduceAdd] using h0012
  exact h0000

end D1Bound5.PairLightAdaptivePrepared28
end
