-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:55:09.741857+00:00
-- url     : https://prove2.me/submissions/1987f96e-5eed-40a9-a4f8-fb3b2c3ca64a

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared35.leftCached.map Prod.fst = PairLightPrepared35.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared35
end
