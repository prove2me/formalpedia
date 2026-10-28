-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:25.037186+00:00
-- url     : https://prove2.me/submissions/da0ba781-fe2b-4d47-9a8e-e357015b767f

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared29.rightCached.map Prod.fst = PairLightPrepared29.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared29
end
