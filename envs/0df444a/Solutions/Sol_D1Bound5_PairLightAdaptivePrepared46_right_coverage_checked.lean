-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:46:14.21133+00:00
-- url     : https://prove2.me/submissions/80ea01a5-c822-4c64-9a63-b424b60aff08

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared46.rightCached.map Prod.fst = PairLightPrepared46.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared46
end
