-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:01:22.187657+00:00
-- url     : https://prove2.me/submissions/d636c947-4db3-4b2c-9dec-2e637c847637

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared43.leftCached.map Prod.fst = PairLightPrepared43.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared43
end
