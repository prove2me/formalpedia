-- Prove2me | solution 1 for D1Bound5.PairLightPrepared21.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:25:18.869089+00:00
-- url     : https://prove2.me/submissions/79b60355-115d-4727-ba9e-f6cfca8c5bc7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData21_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_prefix_003_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 1 sieve rightCached rightRows = true := by
  have h004 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.rightCached004 PairLightAdaptivePrepared21.rightRows004 = true := by
    rfl
  have h003 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.rightCached003 PairLightAdaptivePrepared21.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 189
      PairLightAdaptivePrepared21.rightCached003 PairLightAdaptivePrepared21.rightRows003
      PairLightAdaptivePrepared21.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.rightCached002 PairLightAdaptivePrepared21.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 151
      PairLightAdaptivePrepared21.rightCached002 PairLightAdaptivePrepared21.rightRows002
      PairLightAdaptivePrepared21.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.rightCached001 PairLightAdaptivePrepared21.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 102
      PairLightAdaptivePrepared21.rightCached001 PairLightAdaptivePrepared21.rightRows001
      PairLightAdaptivePrepared21.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 1 1 sieve
      PairLightAdaptivePrepared21.rightCached000 PairLightAdaptivePrepared21.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 1 1 sieve 82
      PairLightAdaptivePrepared21.rightCached000 PairLightAdaptivePrepared21.rightRows000
      PairLightAdaptivePrepared21.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared21
end
