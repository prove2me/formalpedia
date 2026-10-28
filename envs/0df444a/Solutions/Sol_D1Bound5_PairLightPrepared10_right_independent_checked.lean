-- Prove2me | solution 1 for D1Bound5.PairLightPrepared10.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:50:04.779115+00:00
-- url     : https://prove2.me/submissions/041d06cd-2700-4005-b992-7a95e4ee945b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData10_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_000_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_001_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_002_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_003_checked
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_prefix_004_checked
import Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_of_prefix_drop

section
namespace D1Bound5.PairLightPrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 0 1 sieve rightCached rightRows = true := by
  have h005 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.rightCached005 PairLightAdaptivePrepared10.rightRows005 = true := by
    rfl
  have h004 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.rightCached004 PairLightAdaptivePrepared10.rightRows004 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 191
      PairLightAdaptivePrepared10.rightCached004 PairLightAdaptivePrepared10.rightRows004
      PairLightAdaptivePrepared10.right_prefix_004_checked h005
  have h003 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.rightCached003 PairLightAdaptivePrepared10.rightRows003 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 150
      PairLightAdaptivePrepared10.rightCached003 PairLightAdaptivePrepared10.rightRows003
      PairLightAdaptivePrepared10.right_prefix_003_checked h004
  have h002 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.rightCached002 PairLightAdaptivePrepared10.rightRows002 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 102
      PairLightAdaptivePrepared10.rightCached002 PairLightAdaptivePrepared10.rightRows002
      PairLightAdaptivePrepared10.right_prefix_002_checked h003
  have h001 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.rightCached001 PairLightAdaptivePrepared10.rightRows001 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 82
      PairLightAdaptivePrepared10.rightCached001 PairLightAdaptivePrepared10.rightRows001
      PairLightAdaptivePrepared10.right_prefix_001_checked h002
  have h000 : pairLightSelectedFloorIndependentBool 0 1 sieve
      PairLightAdaptivePrepared10.rightCached000 PairLightAdaptivePrepared10.rightRows000 = true :=
    pairLightSelectedFloorIndependentBool_of_prefix_drop 0 1 sieve 71
      PairLightAdaptivePrepared10.rightCached000 PairLightAdaptivePrepared10.rightRows000
      PairLightAdaptivePrepared10.right_prefix_000_checked h001
  exact h000



end D1Bound5.PairLightPrepared10
end
