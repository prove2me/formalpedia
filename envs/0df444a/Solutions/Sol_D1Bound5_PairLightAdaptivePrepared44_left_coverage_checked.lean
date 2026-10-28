-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared44.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:51:17.345449+00:00
-- url     : https://prove2.me/submissions/f5eb9a90-f541-4b28-89e3-2b0ef7d00185

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared44.leftCached.map Prod.fst = PairLightPrepared44.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared44
end
