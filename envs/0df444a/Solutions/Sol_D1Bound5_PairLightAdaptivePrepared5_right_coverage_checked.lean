-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:51.897412+00:00
-- url     : https://prove2.me/submissions/d7589bd9-4270-4f19-8b83-76618cccb691

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared5.rightCached.map Prod.fst = PairLightPrepared5.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared5
end
