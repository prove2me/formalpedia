-- Prove2me | solution 1 for D1Bound5.PairLightPrepared39.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:44:16.872993+00:00
-- url     : https://prove2.me/submissions/95ecead9-9844-4bb6-a76c-8192244fa1b1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData39_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_000_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_002_direct_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 97; every head retains its entire tail. -/
theorem right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 98
      rightCached000 rightRows000 = true := by
  simpa only [rightCached000, rightRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_000_direct_checked

end D1Bound5.PairLightAdaptivePrepared39
end

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 98 through 235; every head retains its entire tail. -/
theorem right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 138
      rightCached001 rightRows001 = true := by
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_001_direct_checked

end D1Bound5.PairLightAdaptivePrepared39
end

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 236 through 455; every head retains its entire tail. -/
theorem right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 220
      rightCached002 rightRows002 = true := by
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_002_direct_checked

end D1Bound5.PairLightAdaptivePrepared39
end

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.rightCached003 PairLightAdaptivePrepared39.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.rightCached002 PairLightAdaptivePrepared39.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 220
      PairLightAdaptivePrepared39.rightCached002 PairLightAdaptivePrepared39.rightRows002
      PairLightAdaptivePrepared39.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.rightCached001 PairLightAdaptivePrepared39.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 138
      PairLightAdaptivePrepared39.rightCached001 PairLightAdaptivePrepared39.rightRows001
      PairLightAdaptivePrepared39.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared39.rightCached000 PairLightAdaptivePrepared39.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 98
      PairLightAdaptivePrepared39.rightCached000 PairLightAdaptivePrepared39.rightRows000
      PairLightAdaptivePrepared39.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared39
end
