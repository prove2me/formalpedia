-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:13.53192+00:00
-- url     : https://prove2.me/submissions/998407d2-26d7-48fa-ac28-d7880918726e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared30.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared30.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared30
end
