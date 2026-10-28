-- Prove2me | solution 1 for D1Bound5.PairLightPrepared46.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:46:03.873985+00:00
-- url     : https://prove2.me/submissions/349be6d4-23d7-47d2-851f-ceac21b4e4c8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 6 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 6 sieve
      PairLightAdaptivePrepared46.rightCached002 PairLightAdaptivePrepared46.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 6 sieve
      PairLightAdaptivePrepared46.rightCached001 PairLightAdaptivePrepared46.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 6 sieve 220
      PairLightAdaptivePrepared46.rightCached001 PairLightAdaptivePrepared46.rightRows001
      PairLightAdaptivePrepared46.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 6 sieve
      PairLightAdaptivePrepared46.rightCached000 PairLightAdaptivePrepared46.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 6 sieve 138
      PairLightAdaptivePrepared46.rightCached000 PairLightAdaptivePrepared46.rightRows000
      PairLightAdaptivePrepared46.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared46
end
