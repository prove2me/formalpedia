-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:13.145002+00:00
-- url     : https://prove2.me/submissions/4341e23d-eb59-46d0-8e6e-7e9f818452e4

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared1.rightCached.map Prod.fst = PairLightPrepared1.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared1
end
