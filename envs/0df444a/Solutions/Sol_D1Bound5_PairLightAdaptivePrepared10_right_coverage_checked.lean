-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:36.955271+00:00
-- url     : https://prove2.me/submissions/39e13dbb-0173-44cc-8f4a-d7e960d491ba

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared10.rightCached.map Prod.fst = PairLightPrepared10.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared10
end
