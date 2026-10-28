-- Prove2me | solution 1 for D1Bound5.PairLightPrepared24.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:24.649304+00:00
-- url     : https://prove2.me/submissions/c8b38290-1b87-4c45-a091-550f97dbf1d3

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData24_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_000_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_001_direct_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_002_direct_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 100; every head retains its entire tail. -/
theorem right_prefix_000_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 101
      rightCached000 rightRows000 = true := by
  simpa only [rightCached000, rightRows000, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_000_direct_checked

end D1Bound5.PairLightAdaptivePrepared24
end

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 101 through 247; every head retains its entire tail. -/
theorem right_prefix_001_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 147
      rightCached001 rightRows001 = true := by
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_001_direct_checked

end D1Bound5.PairLightAdaptivePrepared24
end

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 248 through 445; every head retains its entire tail. -/
theorem right_prefix_002_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 198
      rightCached002 rightRows002 = true := by
  simpa only [rightCached000, rightRows000, rightCached001, rightRows001, rightCached002, rightRows002, List.drop_drop, Nat.reduceAdd, List.drop_zero] using
    right_prefix_002_direct_checked

end D1Bound5.PairLightAdaptivePrepared24
end

section
namespace D1Bound5.PairLightPrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared24.rightCached003 PairLightAdaptivePrepared24.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared24.rightCached002 PairLightAdaptivePrepared24.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 198
      PairLightAdaptivePrepared24.rightCached002 PairLightAdaptivePrepared24.rightRows002
      PairLightAdaptivePrepared24.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared24.rightCached001 PairLightAdaptivePrepared24.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 147
      PairLightAdaptivePrepared24.rightCached001 PairLightAdaptivePrepared24.rightRows001
      PairLightAdaptivePrepared24.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared24.rightCached000 PairLightAdaptivePrepared24.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 101
      PairLightAdaptivePrepared24.rightCached000 PairLightAdaptivePrepared24.rightRows000
      PairLightAdaptivePrepared24.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared24
end
