-- Prove2me | solution 1 for D1Bound5.PairLightPrepared5.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:07.973737+00:00
-- url     : https://prove2.me/submissions/a04f76f6-a819-44e9-8c79-b86bd73a51c6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared5.left_coverage_checked







end D1Bound5.PairLightPrepared5
end
