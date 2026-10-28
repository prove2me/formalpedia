-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:03.985978+00:00
-- url     : https://prove2.me/submissions/6a3ed2cf-3c0b-4a82-bb91-e7c3caf29c60

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared6.rightCached.map Prod.fst = PairLightPrepared6.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared6
end
