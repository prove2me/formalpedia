-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:04.556992+00:00
-- url     : https://prove2.me/submissions/d8219cac-39f3-4228-b7d4-c54f04ba3f5f

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared1.leftCached.map Prod.fst = PairLightPrepared1.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared1
end
