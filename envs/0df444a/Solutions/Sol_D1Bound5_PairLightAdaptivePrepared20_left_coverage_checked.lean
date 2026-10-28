-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared20.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:33.476226+00:00
-- url     : https://prove2.me/submissions/a0235106-bc2a-4ad0-a7df-8a826b7e3b95

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared20.leftCached.map Prod.fst = PairLightPrepared20.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared20
end
