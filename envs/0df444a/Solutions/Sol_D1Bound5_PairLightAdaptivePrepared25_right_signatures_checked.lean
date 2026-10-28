-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:14.917985+00:00
-- url     : https://prove2.me/submissions/56bc386d-8170-418a-a006-51cba5f52334

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared25.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared25.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared25
end
