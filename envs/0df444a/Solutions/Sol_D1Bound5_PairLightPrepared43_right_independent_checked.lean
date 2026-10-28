-- Prove2me | solution 1 for D1Bound5.PairLightPrepared43.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:42:34.850119+00:00
-- url     : https://prove2.me/submissions/91ca99a2-8684-4946-afd8-c47461d1f48d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData43_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_000_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_001_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_prefix_002_direct_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 91; every head retains its entire tail. -/
theorem right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 92
      rightCached000 rightRows000 = true := by
  simpa only [rightCached000, rightRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_000_direct_checked

end D1Bound5.PairLightAdaptivePrepared43
end

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 92 through 213; every head retains its entire tail. -/
theorem right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 122
      rightCached001 rightRows001 = true := by
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_001_direct_checked

end D1Bound5.PairLightAdaptivePrepared43
end

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 214 through 479; every head retains its entire tail. -/
theorem right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 266
      rightCached002 rightRows002 = true := by
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_002_direct_checked

end D1Bound5.PairLightAdaptivePrepared43
end

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 3 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.rightCached003 PairLightAdaptivePrepared43.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.rightCached002 PairLightAdaptivePrepared43.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 266
      PairLightAdaptivePrepared43.rightCached002 PairLightAdaptivePrepared43.rightRows002
      PairLightAdaptivePrepared43.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.rightCached001 PairLightAdaptivePrepared43.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 122
      PairLightAdaptivePrepared43.rightCached001 PairLightAdaptivePrepared43.rightRows001
      PairLightAdaptivePrepared43.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared43.rightCached000 PairLightAdaptivePrepared43.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 92
      PairLightAdaptivePrepared43.rightCached000 PairLightAdaptivePrepared43.rightRows000
      PairLightAdaptivePrepared43.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared43
end
