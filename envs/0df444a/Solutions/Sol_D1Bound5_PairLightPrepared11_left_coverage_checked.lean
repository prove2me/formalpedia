-- Prove2me | solution 1 for D1Bound5.PairLightPrepared11.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:29.442637+00:00
-- url     : https://prove2.me/submissions/43aa1437-af9e-4096-a971-3223736467df

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared11.left_coverage_checked







end D1Bound5.PairLightPrepared11
end
