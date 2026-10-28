-- Prove2me | solution 1 for D1Bound5.PairLightPrepared43.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:41:38.140408+00:00
-- url     : https://prove2.me/submissions/126e6d34-98a6-4206-a285-a781b539e680

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData43_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_000_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_001_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_prefix_002_direct_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 90; every head retains its entire tail. -/
theorem left_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 91
      leftCached000 leftRows000 = true := by
  simpa only [leftCached000, leftRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    left_prefix_000_direct_checked

end D1Bound5.PairLightAdaptivePrepared43
end

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 91 through 211; every head retains its entire tail. -/
theorem left_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 121
      leftCached001 leftRows001 = true := by
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    left_prefix_001_direct_checked

end D1Bound5.PairLightAdaptivePrepared43
end

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 212 through 481; every head retains its entire tail. -/
theorem left_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 270
      leftCached002 leftRows002 = true := by
  simpa only [leftCached000, leftRows000, leftCached001, leftRows001, leftCached002, leftRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    left_prefix_002_direct_checked

end D1Bound5.PairLightAdaptivePrepared43
end

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 3 sieve leftCached leftRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.leftCached003 PairLightAdaptivePrepared43.leftRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.leftCached002 PairLightAdaptivePrepared43.leftRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 270
      PairLightAdaptivePrepared43.leftCached002 PairLightAdaptivePrepared43.leftRows002
      PairLightAdaptivePrepared43.left_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.leftCached001 PairLightAdaptivePrepared43.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 121
      PairLightAdaptivePrepared43.leftCached001 PairLightAdaptivePrepared43.leftRows001
      PairLightAdaptivePrepared43.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.leftCached000 PairLightAdaptivePrepared43.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 91
      PairLightAdaptivePrepared43.leftCached000 PairLightAdaptivePrepared43.leftRows000
      PairLightAdaptivePrepared43.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared43
end
