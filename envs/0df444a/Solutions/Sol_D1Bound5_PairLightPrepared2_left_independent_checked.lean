-- Prove2me | solution 1 for D1Bound5.PairLightPrepared2.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:45:10.969833+00:00
-- url     : https://prove2.me/submissions/96f7272a-207a-4b96-ba1c-f5a385f1378e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData2_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_left_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve leftCached leftRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared2.leftCached001 PairLightAdaptivePrepared2.leftRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared2.leftCached000 PairLightAdaptivePrepared2.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 207
      PairLightAdaptivePrepared2.leftCached000 PairLightAdaptivePrepared2.leftRows000
      PairLightAdaptivePrepared2.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared2
end
