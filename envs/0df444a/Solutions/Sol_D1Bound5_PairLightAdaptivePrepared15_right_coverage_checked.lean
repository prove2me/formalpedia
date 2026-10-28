-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:57.239431+00:00
-- url     : https://prove2.me/submissions/014c8612-3097-4eab-9144-f2fe9f9ac4ee

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared15.rightCached.map Prod.fst = PairLightPrepared15.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared15
end
