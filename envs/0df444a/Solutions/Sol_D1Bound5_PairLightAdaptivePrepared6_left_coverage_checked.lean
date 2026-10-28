-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:07.580058+00:00
-- url     : https://prove2.me/submissions/c94b277f-b617-423a-9f55-dd8ebac62fa5

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared6.leftCached.map Prod.fst = PairLightPrepared6.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared6
end
