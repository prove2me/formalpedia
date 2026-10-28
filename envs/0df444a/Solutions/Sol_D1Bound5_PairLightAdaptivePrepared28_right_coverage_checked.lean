-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:46.210987+00:00
-- url     : https://prove2.me/submissions/2f5992b5-41e6-41f2-b072-55d98465f184

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared28.rightCached.map Prod.fst = PairLightPrepared28.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared28
end
