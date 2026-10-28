-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:02.852223+00:00
-- url     : https://prove2.me/submissions/17b74100-fa13-4d3d-aec6-12027b10c232

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared17.rightCached.map Prod.fst = PairLightPrepared17.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared17
end
