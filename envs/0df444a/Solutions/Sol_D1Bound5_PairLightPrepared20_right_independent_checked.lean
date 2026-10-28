-- Prove2me | solution 1 for D1Bound5.PairLightPrepared20.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:56:28.215355+00:00
-- url     : https://prove2.me/submissions/385c39fc-86a6-47ee-a447-9eb82d857b97

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_right_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared20.rightCached001 PairLightAdaptivePrepared20.rightRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared20.rightCached000 PairLightAdaptivePrepared20.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 223
      PairLightAdaptivePrepared20.rightCached000 PairLightAdaptivePrepared20.rightRows000
      PairLightAdaptivePrepared20.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared20
end
