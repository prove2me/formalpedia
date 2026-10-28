-- Prove2me | solution 1 for D1Bound5.PairLightPrepared13.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:43:28.490978+00:00
-- url     : https://prove2.me/submissions/601ed994-4fc9-4f9b-8d17-c1933e151342

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData13_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared13_right_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 2 sieve rightCached rightRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared13.rightCached001 PairLightAdaptivePrepared13.rightRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared13.rightCached000 PairLightAdaptivePrepared13.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 248
      PairLightAdaptivePrepared13.rightCached000 PairLightAdaptivePrepared13.rightRows000
      PairLightAdaptivePrepared13.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared13
end
