-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:13.6972+00:00
-- url     : https://prove2.me/submissions/82b63363-acd4-470d-9a95-59e45119e83e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared39.rightCached.map Prod.fst = PairLightPrepared39.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared39
end
