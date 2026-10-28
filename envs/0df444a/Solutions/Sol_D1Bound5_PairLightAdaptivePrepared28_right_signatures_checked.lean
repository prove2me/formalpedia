-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:46.910951+00:00
-- url     : https://prove2.me/submissions/4d5d603e-9a6d-43ae-8a2c-e064d106a3c5

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared28.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared28.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared28
end
