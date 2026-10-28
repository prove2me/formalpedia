-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:26.717489+00:00
-- url     : https://prove2.me/submissions/5c8f185d-7aad-4702-96ae-375ab7ddb46e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared15.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared15.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared15
end
