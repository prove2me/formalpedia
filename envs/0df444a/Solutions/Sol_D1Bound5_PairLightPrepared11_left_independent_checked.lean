-- Prove2me | solution 1 for D1Bound5.PairLightPrepared11.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:42:35.892987+00:00
-- url     : https://prove2.me/submissions/b8234754-685c-4c65-b84d-879f9141c97b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared11.leftCached002 PairLightAdaptivePrepared11.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared11.leftCached001 PairLightAdaptivePrepared11.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 221
      PairLightAdaptivePrepared11.leftCached001 PairLightAdaptivePrepared11.leftRows001
      PairLightAdaptivePrepared11.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared11.leftCached000 PairLightAdaptivePrepared11.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 138
      PairLightAdaptivePrepared11.leftCached000 PairLightAdaptivePrepared11.leftRows000
      PairLightAdaptivePrepared11.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared11
end
