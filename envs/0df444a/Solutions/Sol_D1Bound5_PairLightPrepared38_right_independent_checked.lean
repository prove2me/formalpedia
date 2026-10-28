-- Prove2me | solution 1 for D1Bound5.PairLightPrepared38.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:40:45.87293+00:00
-- url     : https://prove2.me/submissions/77795684-0e20-4bcc-83fa-ff9adbbf674f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared38.rightCached001 PairLightAdaptivePrepared38.rightRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared38.rightCached000 PairLightAdaptivePrepared38.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 281
      PairLightAdaptivePrepared38.rightCached000 PairLightAdaptivePrepared38.rightRows000
      PairLightAdaptivePrepared38.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared38
end
