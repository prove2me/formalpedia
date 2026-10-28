-- Prove2me | solution 1 for D1Bound5.PairLightPrepared18.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:45:08.28253+00:00
-- url     : https://prove2.me/submissions/7a119cd3-7844-46be-b366-fbec5341b740

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared18.rightCached001 PairLightAdaptivePrepared18.rightRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared18.rightCached000 PairLightAdaptivePrepared18.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 262
      PairLightAdaptivePrepared18.rightCached000 PairLightAdaptivePrepared18.rightRows000
      PairLightAdaptivePrepared18.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared18
end
