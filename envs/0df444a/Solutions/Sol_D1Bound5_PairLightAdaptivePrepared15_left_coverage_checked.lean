-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:24.123135+00:00
-- url     : https://prove2.me/submissions/ea8b1851-20a0-43ad-8ea8-b8b32f8d0965

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared15.leftCached.map Prod.fst = PairLightPrepared15.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared15
end
