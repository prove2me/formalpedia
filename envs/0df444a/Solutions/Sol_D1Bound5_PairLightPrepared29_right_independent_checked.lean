-- Prove2me | solution 1 for D1Bound5.PairLightPrepared29.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:54:13.990984+00:00
-- url     : https://prove2.me/submissions/e50defea-40ff-4212-8202-6a25e0ad0f30

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared29.rightCached002 PairLightAdaptivePrepared29.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared29.rightCached001 PairLightAdaptivePrepared29.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 256
      PairLightAdaptivePrepared29.rightCached001 PairLightAdaptivePrepared29.rightRows001
      PairLightAdaptivePrepared29.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared29.rightCached000 PairLightAdaptivePrepared29.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 125
      PairLightAdaptivePrepared29.rightCached000 PairLightAdaptivePrepared29.rightRows000
      PairLightAdaptivePrepared29.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared29
end
