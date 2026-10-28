-- Prove2me | solution 1 for D1Bound5.PairLightPrepared9.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:29.176449+00:00
-- url     : https://prove2.me/submissions/0fce1505-a1ca-4a3d-bbdf-3a28a209d832

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData9_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_left_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared9.leftCached001 PairLightAdaptivePrepared9.leftRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared9.leftCached000 PairLightAdaptivePrepared9.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 219
      PairLightAdaptivePrepared9.leftCached000 PairLightAdaptivePrepared9.leftRows000
      PairLightAdaptivePrepared9.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared9
end
