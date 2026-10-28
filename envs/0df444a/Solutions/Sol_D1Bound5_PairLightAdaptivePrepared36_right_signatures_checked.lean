-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:28:59.060427+00:00
-- url     : https://prove2.me/submissions/a8dd6241-168b-43a8-83df-945b213f6e1c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared36.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared36.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared36
end
