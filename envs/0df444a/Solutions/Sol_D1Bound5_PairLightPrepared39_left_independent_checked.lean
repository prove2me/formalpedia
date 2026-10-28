-- Prove2me | solution 1 for D1Bound5.PairLightPrepared39.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:56:20.891951+00:00
-- url     : https://prove2.me/submissions/f908ec23-27fd-4822-8e83-9636688b9c64

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData39_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_002_direct_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 96; every head retains its entire tail. -/
theorem left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 97
      leftCached000 leftRows000 = true := by
  simpa only [leftCached000, leftRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    left_prefix_000_direct_checked

end D1Bound5.PairLightAdaptivePrepared39
end

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 97 through 232; every head retains its entire tail. -/
theorem left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 136
      leftCached001 leftRows001 = true := by
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    left_prefix_001_direct_checked

end D1Bound5.PairLightAdaptivePrepared39
end

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 233 through 457; every head retains its entire tail. -/
theorem left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 225
      leftCached002 leftRows002 = true := by
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    left_prefix_002_direct_checked

end D1Bound5.PairLightAdaptivePrepared39
end

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.leftCached003 PairLightAdaptivePrepared39.leftRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.leftCached002 PairLightAdaptivePrepared39.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 225
      PairLightAdaptivePrepared39.leftCached002 PairLightAdaptivePrepared39.leftRows002
      PairLightAdaptivePrepared39.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.leftCached001 PairLightAdaptivePrepared39.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 136
      PairLightAdaptivePrepared39.leftCached001 PairLightAdaptivePrepared39.leftRows001
      PairLightAdaptivePrepared39.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.leftCached000 PairLightAdaptivePrepared39.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 97
      PairLightAdaptivePrepared39.leftCached000 PairLightAdaptivePrepared39.leftRows000
      PairLightAdaptivePrepared39.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared39
end
