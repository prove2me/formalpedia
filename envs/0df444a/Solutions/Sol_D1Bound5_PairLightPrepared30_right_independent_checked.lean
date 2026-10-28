-- Prove2me | solution 1 for D1Bound5.PairLightPrepared30.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:47:54.165967+00:00
-- url     : https://prove2.me/submissions/7b082200-b96f-4bd2-a770-5875cf312300

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData30_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_prefix_002_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.rightCached003 PairLightAdaptivePrepared30.rightRows003 = true := by
    rfl
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.rightCached002 PairLightAdaptivePrepared30.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 266
      PairLightAdaptivePrepared30.rightCached002 PairLightAdaptivePrepared30.rightRows002
      PairLightAdaptivePrepared30.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.rightCached001 PairLightAdaptivePrepared30.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 122
      PairLightAdaptivePrepared30.rightCached001 PairLightAdaptivePrepared30.rightRows001
      PairLightAdaptivePrepared30.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared30.rightCached000 PairLightAdaptivePrepared30.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 92
      PairLightAdaptivePrepared30.rightCached000 PairLightAdaptivePrepared30.rightRows000
      PairLightAdaptivePrepared30.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared30
end
