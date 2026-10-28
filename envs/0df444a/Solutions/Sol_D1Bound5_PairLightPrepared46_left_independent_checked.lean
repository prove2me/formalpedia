-- Prove2me | solution 1 for D1Bound5.PairLightPrepared46.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:45:13.525271+00:00
-- url     : https://prove2.me/submissions/6c12333c-b366-49cc-add7-9db3f82c302c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 6 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 6 sieve
      PairLightAdaptivePrepared46.leftCached002 PairLightAdaptivePrepared46.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 6 sieve
      PairLightAdaptivePrepared46.leftCached001 PairLightAdaptivePrepared46.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 6 sieve 223
      PairLightAdaptivePrepared46.leftCached001 PairLightAdaptivePrepared46.leftRows001
      PairLightAdaptivePrepared46.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 6 sieve
      PairLightAdaptivePrepared46.leftCached000 PairLightAdaptivePrepared46.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 6 sieve 137
      PairLightAdaptivePrepared46.leftCached000 PairLightAdaptivePrepared46.leftRows000
      PairLightAdaptivePrepared46.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared46
end
