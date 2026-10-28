-- Prove2me | solution 1 for D1Bound5.PairLightPrepared36.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:08.447711+00:00
-- url     : https://prove2.me/submissions/87de1f27-b28c-4294-9f74-b9c3afe81721

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData36_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_right_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 2 sieve rightCached rightRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.rightCached004 PairLightAdaptivePrepared36.rightRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.rightCached003 PairLightAdaptivePrepared36.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 273
      PairLightAdaptivePrepared36.rightCached003 PairLightAdaptivePrepared36.rightRows003
      PairLightAdaptivePrepared36.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.rightCached002 PairLightAdaptivePrepared36.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 120
      PairLightAdaptivePrepared36.rightCached002 PairLightAdaptivePrepared36.rightRows002
      PairLightAdaptivePrepared36.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.rightCached001 PairLightAdaptivePrepared36.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 91
      PairLightAdaptivePrepared36.rightCached001 PairLightAdaptivePrepared36.rightRows001
      PairLightAdaptivePrepared36.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 2 sieve
      PairLightAdaptivePrepared36.rightCached000 PairLightAdaptivePrepared36.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 2 sieve 76
      PairLightAdaptivePrepared36.rightCached000 PairLightAdaptivePrepared36.rightRows000
      PairLightAdaptivePrepared36.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared36
end
