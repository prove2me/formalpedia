-- Prove2me | solution 1 for D1Bound5.PairLightPrepared44.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:41:36.51607+00:00
-- url     : https://prove2.me/submissions/37feae84-1c17-4e0b-8861-2fa97d8d52e5

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData44_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_left_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 4 sieve leftCached leftRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 4 sieve
      PairLightAdaptivePrepared44.leftCached001 PairLightAdaptivePrepared44.leftRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 4 sieve
      PairLightAdaptivePrepared44.leftCached000 PairLightAdaptivePrepared44.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 4 sieve 220
      PairLightAdaptivePrepared44.leftCached000 PairLightAdaptivePrepared44.leftRows000
      PairLightAdaptivePrepared44.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared44
end
