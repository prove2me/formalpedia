-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:39.003856+00:00
-- url     : https://prove2.me/submissions/f5ee1e5b-906a-4cc7-bd8e-1a4d81c724c0

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared11.leftCached.map Prod.fst = PairLightPrepared11.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared11
end
