-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:35.301739+00:00
-- url     : https://prove2.me/submissions/ab19152d-8f2f-4922-8e05-fdbeb710810f

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared23.leftCached.map Prod.fst = PairLightPrepared23.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared23
end
