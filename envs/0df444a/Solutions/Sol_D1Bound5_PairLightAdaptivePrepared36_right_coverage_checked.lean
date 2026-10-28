-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:41:01.847734+00:00
-- url     : https://prove2.me/submissions/0d8edfa9-30b7-4554-9895-bbc935b1c822

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared36.rightCached.map Prod.fst = PairLightPrepared36.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared36
end
