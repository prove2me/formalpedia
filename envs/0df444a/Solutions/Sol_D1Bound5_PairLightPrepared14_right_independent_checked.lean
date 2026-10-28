-- Prove2me | solution 1 for D1Bound5.PairLightPrepared14.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:54.802457+00:00
-- url     : https://prove2.me/submissions/d53e05aa-7059-40bb-980f-076357fcfee7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData14_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 2 sieve rightCached rightRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.rightCached004 PairLightAdaptivePrepared14.rightRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.rightCached003 PairLightAdaptivePrepared14.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 79
      PairLightAdaptivePrepared14.rightCached003 PairLightAdaptivePrepared14.rightRows003
      PairLightAdaptivePrepared14.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.rightCached002 PairLightAdaptivePrepared14.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 215
      PairLightAdaptivePrepared14.rightCached002 PairLightAdaptivePrepared14.rightRows002
      PairLightAdaptivePrepared14.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.rightCached001 PairLightAdaptivePrepared14.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 114
      PairLightAdaptivePrepared14.rightCached001 PairLightAdaptivePrepared14.rightRows001
      PairLightAdaptivePrepared14.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 2 sieve
      PairLightAdaptivePrepared14.rightCached000 PairLightAdaptivePrepared14.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 2 sieve 88
      PairLightAdaptivePrepared14.rightCached000 PairLightAdaptivePrepared14.rightRows000
      PairLightAdaptivePrepared14.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared14
end
