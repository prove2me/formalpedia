-- Prove2me | solution 1 for D1Bound5.PairLightPrepared15.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:55.635894+00:00
-- url     : https://prove2.me/submissions/4ec35b02-697e-4656-97b0-122da2486261

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData15_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 2 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.rightCached003 PairLightAdaptivePrepared15.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.rightCached002 PairLightAdaptivePrepared15.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 266
      PairLightAdaptivePrepared15.rightCached002 PairLightAdaptivePrepared15.rightRows002
      PairLightAdaptivePrepared15.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.rightCached001 PairLightAdaptivePrepared15.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 122
      PairLightAdaptivePrepared15.rightCached001 PairLightAdaptivePrepared15.rightRows001
      PairLightAdaptivePrepared15.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared15.rightCached000 PairLightAdaptivePrepared15.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 92
      PairLightAdaptivePrepared15.rightCached000 PairLightAdaptivePrepared15.rightRows000
      PairLightAdaptivePrepared15.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared15
end
