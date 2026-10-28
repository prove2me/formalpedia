-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:09.20068+00:00
-- url     : https://prove2.me/submissions/3bd6fec8-2aa9-47ad-a04f-c9788b2f14a3

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared28.leftCached.map Prod.fst = PairLightPrepared28.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared28
end
