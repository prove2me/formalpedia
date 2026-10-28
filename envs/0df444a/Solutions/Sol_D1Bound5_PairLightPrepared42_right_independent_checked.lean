-- Prove2me | solution 1 for D1Bound5.PairLightPrepared42.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:39:43.927413+00:00
-- url     : https://prove2.me/submissions/c99bdeeb-1354-4317-84c5-08bb54d71a71

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData42_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared42_right_prefix_000_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 3 sieve rightCached rightRows = true := by
  have h001 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared42.rightCached001 PairLightAdaptivePrepared42.rightRows001 = true := by
    rfl
  have h000 : pairLightSelectedFloorIndependentBool 1 3 sieve
      PairLightAdaptivePrepared42.rightCached000 PairLightAdaptivePrepared42.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 3 sieve 242
      PairLightAdaptivePrepared42.rightCached000 PairLightAdaptivePrepared42.rightRows000
      PairLightAdaptivePrepared42.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared42
end
