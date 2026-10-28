-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:43.363972+00:00
-- url     : https://prove2.me/submissions/4b0f9021-6a15-4d56-9b57-4afba70e27f1

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared21.rightCached.map Prod.fst = PairLightPrepared21.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared21
end
