-- Prove2me | solution 1 for D1Bound5.PairLightPrepared23.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:54:24.089441+00:00
-- url     : https://prove2.me/submissions/41e08cdd-dabd-4000-b6af-24b6be2dea25

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData23_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared23.rightCached003 PairLightAdaptivePrepared23.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared23.rightCached002 PairLightAdaptivePrepared23.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 266
      PairLightAdaptivePrepared23.rightCached002 PairLightAdaptivePrepared23.rightRows002
      PairLightAdaptivePrepared23.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared23.rightCached001 PairLightAdaptivePrepared23.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 122
      PairLightAdaptivePrepared23.rightCached001 PairLightAdaptivePrepared23.rightRows001
      PairLightAdaptivePrepared23.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared23.rightCached000 PairLightAdaptivePrepared23.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 92
      PairLightAdaptivePrepared23.rightCached000 PairLightAdaptivePrepared23.rightRows000
      PairLightAdaptivePrepared23.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared23
end
