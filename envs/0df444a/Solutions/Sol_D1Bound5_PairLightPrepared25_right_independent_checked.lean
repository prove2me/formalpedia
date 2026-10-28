-- Prove2me | solution 1 for D1Bound5.PairLightPrepared25.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:43:29.363985+00:00
-- url     : https://prove2.me/submissions/8e4aef66-4e95-414c-abb4-a889679862d4

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_prefix_001_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared25.rightCached002 PairLightAdaptivePrepared25.rightRows002 = true := by
    rfl
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared25.rightCached001 PairLightAdaptivePrepared25.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 256
      PairLightAdaptivePrepared25.rightCached001 PairLightAdaptivePrepared25.rightRows001
      PairLightAdaptivePrepared25.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared25.rightCached000 PairLightAdaptivePrepared25.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 125
      PairLightAdaptivePrepared25.rightCached000 PairLightAdaptivePrepared25.rightRows000
      PairLightAdaptivePrepared25.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared25
end
