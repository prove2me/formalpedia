-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:39.694279+00:00
-- url     : https://prove2.me/submissions/1ab623da-0134-48ed-bf53-d0760d49f8a6

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared19.rightCached.map Prod.fst = PairLightPrepared19.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared19
end
