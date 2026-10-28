-- Prove2me | solution 1 for D1Bound5.PairLightPrepared47.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:12.428931+00:00
-- url     : https://prove2.me/submissions/2e7a00d2-f93f-40db-95bd-a89e1dad2a87

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_002

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true := by
  decide +kernel







end D1Bound5.PairLightPrepared47
end
