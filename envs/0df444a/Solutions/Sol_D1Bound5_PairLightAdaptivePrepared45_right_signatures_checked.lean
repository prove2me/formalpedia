-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared45.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:52.900274+00:00
-- url     : https://prove2.me/submissions/1552e94e-3dc8-4756-8535-51fb6e3503f0

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared45.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared45.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared45
end
