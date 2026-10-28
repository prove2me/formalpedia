-- Prove2me | solution 1 for D1Bound5.PairLightPrepared18.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:22:58.964724+00:00
-- url     : https://prove2.me/submissions/ec07d476-b423-4d64-899a-7171eb593f78

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared18.right_coverage_checked







end D1Bound5.PairLightPrepared18
end
