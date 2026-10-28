-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:32.848699+00:00
-- url     : https://prove2.me/submissions/c30bc1d1-d3a3-47c1-b282-2c358321ba21

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared21.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared21.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared21
end
