-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:37.26659+00:00
-- url     : https://prove2.me/submissions/ea55d4dc-315d-484e-87e5-d27c3d94b18c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared1.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared1.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared1
end
