-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:02.255996+00:00
-- url     : https://prove2.me/submissions/aff80f08-5cdc-403b-90c0-14548529e0b9

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared8.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared8.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared8
end
