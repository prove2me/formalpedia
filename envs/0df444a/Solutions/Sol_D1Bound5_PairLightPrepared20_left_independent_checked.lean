-- Prove2me | solution 1 for D1Bound5.PairLightPrepared20.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:45:10.151816+00:00
-- url     : https://prove2.me/submissions/d3285229-4cdc-4d92-8487-4a27ba0d4d38

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_left_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared20.leftCached001 PairLightAdaptivePrepared20.leftRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared20.leftCached000 PairLightAdaptivePrepared20.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 223
      PairLightAdaptivePrepared20.leftCached000 PairLightAdaptivePrepared20.leftRows000
      PairLightAdaptivePrepared20.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared20
end
