-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:33.72899+00:00
-- url     : https://prove2.me/submissions/3ef0599e-888c-48b2-ae07-dba76bcaa2a2

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared36.leftCached.map Prod.fst = PairLightPrepared36.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared36
end
