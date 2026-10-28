-- Prove2me | solution 1 for D1Bound5.PairLightPrepared38.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:46:59.984492+00:00
-- url     : https://prove2.me/submissions/139c967f-7737-47ae-8116-e7506fa8755d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve leftCached leftRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared38.leftCached001 PairLightAdaptivePrepared38.leftRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared38.leftCached000 PairLightAdaptivePrepared38.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 280
      PairLightAdaptivePrepared38.leftCached000 PairLightAdaptivePrepared38.leftRows000
      PairLightAdaptivePrepared38.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared38
end
