-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:00.372213+00:00
-- url     : https://prove2.me/submissions/e2cd1a0a-0eb3-47b6-a715-9ee531d296f5

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared26.leftCached.map Prod.fst = PairLightPrepared26.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared26
end
