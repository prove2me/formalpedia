-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:36.044048+00:00
-- url     : https://prove2.me/submissions/dcc96eb3-66a6-459c-8d3a-46f298b94c54

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared3.rightCached.map Prod.fst = PairLightPrepared3.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared3
end
