-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:07.341022+00:00
-- url     : https://prove2.me/submissions/17153059-0713-451a-84cc-12151d893112

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared23.rightCached.map Prod.fst = PairLightPrepared23.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared23
end
