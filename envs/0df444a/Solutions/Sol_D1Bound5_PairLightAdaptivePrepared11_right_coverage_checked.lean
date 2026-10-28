-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:47.86792+00:00
-- url     : https://prove2.me/submissions/d3928d37-9b31-4bc6-9b1f-4b244ca41399

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared11.rightCached.map Prod.fst = PairLightPrepared11.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared11
end
