-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:25.824071+00:00
-- url     : https://prove2.me/submissions/7b350c31-d614-4915-ba76-78cd4fbba682

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared4.rightCached.map Prod.fst = PairLightPrepared4.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared4
end
