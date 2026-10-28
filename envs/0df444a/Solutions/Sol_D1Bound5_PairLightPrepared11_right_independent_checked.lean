-- Prove2me | solution 1 for D1Bound5.PairLightPrepared11.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:53:50.392969+00:00
-- url     : https://prove2.me/submissions/2d6f476d-067b-4e6b-8819-4adcac2c3d49

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared11.rightCached002 PairLightAdaptivePrepared11.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared11.rightCached001 PairLightAdaptivePrepared11.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 221
      PairLightAdaptivePrepared11.rightCached001 PairLightAdaptivePrepared11.rightRows001
      PairLightAdaptivePrepared11.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared11.rightCached000 PairLightAdaptivePrepared11.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 138
      PairLightAdaptivePrepared11.rightCached000 PairLightAdaptivePrepared11.rightRows000
      PairLightAdaptivePrepared11.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared11
end
