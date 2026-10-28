-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:07:51.164008+00:00
-- url     : https://prove2.me/submissions/d52a0fbe-19c7-4706-aeed-0bb3f87cbe35

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared8.leftCached.map Prod.fst = PairLightPrepared8.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared8
end
