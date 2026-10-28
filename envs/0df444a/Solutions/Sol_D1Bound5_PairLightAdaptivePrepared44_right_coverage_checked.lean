-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared44.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:35.176773+00:00
-- url     : https://prove2.me/submissions/d7ecf1ab-c37b-444d-8b3d-c345f74dce06

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared44.rightCached.map Prod.fst = PairLightPrepared44.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared44
end
