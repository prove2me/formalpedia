-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared45.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:36.823786+00:00
-- url     : https://prove2.me/submissions/6e18a567-0b3e-494e-a591-e955cfa945c4

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared45.rightCached.map Prod.fst = PairLightPrepared45.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared45
end
