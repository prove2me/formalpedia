-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:57.085992+00:00
-- url     : https://prove2.me/submissions/793ebfed-f497-40f8-a4cb-10b355808482

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared5.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared5.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared5
end
