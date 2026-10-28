-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:27.346531+00:00
-- url     : https://prove2.me/submissions/1b0c6a27-d4a3-4c05-8ff6-5a2f10e87df4

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared8.rightCached.map Prod.fst = PairLightPrepared8.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared8
end
