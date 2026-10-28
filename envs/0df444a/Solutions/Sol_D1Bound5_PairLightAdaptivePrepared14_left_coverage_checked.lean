-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:44.623084+00:00
-- url     : https://prove2.me/submissions/957fc0ac-da32-438b-bb8d-b2273347e24e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared14.leftCached.map Prod.fst = PairLightPrepared14.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared14
end
