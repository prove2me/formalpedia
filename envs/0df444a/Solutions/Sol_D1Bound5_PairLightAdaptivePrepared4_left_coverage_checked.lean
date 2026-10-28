-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:41.710434+00:00
-- url     : https://prove2.me/submissions/fc80aefa-7334-4524-9fc7-5b5870c856d5

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared4.leftCached.map Prod.fst = PairLightPrepared4.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared4
end
