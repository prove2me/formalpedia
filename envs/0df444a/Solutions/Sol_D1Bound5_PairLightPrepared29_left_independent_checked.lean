-- Prove2me | solution 1 for D1Bound5.PairLightPrepared29.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:47:53.311663+00:00
-- url     : https://prove2.me/submissions/9ef22a16-6368-415f-bc39-048bb72cfcf6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve leftCached leftRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared29.leftCached002 PairLightAdaptivePrepared29.leftRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared29.leftCached001 PairLightAdaptivePrepared29.leftRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 254
      PairLightAdaptivePrepared29.leftCached001 PairLightAdaptivePrepared29.leftRows001
      PairLightAdaptivePrepared29.left_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared29.leftCached000 PairLightAdaptivePrepared29.leftRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 126
      PairLightAdaptivePrepared29.leftCached000 PairLightAdaptivePrepared29.leftRows000
      PairLightAdaptivePrepared29.left_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared29
end
