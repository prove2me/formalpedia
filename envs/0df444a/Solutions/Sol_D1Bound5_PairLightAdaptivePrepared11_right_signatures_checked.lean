-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:12.039048+00:00
-- url     : https://prove2.me/submissions/eaedc939-d979-4c51-9d87-957bb0e70bdc

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared11.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared11.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared11
end
