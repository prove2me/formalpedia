-- Prove2me | solution 1 for D1Bound5.PairLightPrepared9.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:26:28.619153+00:00
-- url     : https://prove2.me/submissions/abf0650d-b3ca-47c4-9521-f4a6583389bf

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData9_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_right_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared9.rightCached001 PairLightAdaptivePrepared9.rightRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared9.rightCached000 PairLightAdaptivePrepared9.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 219
      PairLightAdaptivePrepared9.rightCached000 PairLightAdaptivePrepared9.rightRows000
      PairLightAdaptivePrepared9.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared9
end
