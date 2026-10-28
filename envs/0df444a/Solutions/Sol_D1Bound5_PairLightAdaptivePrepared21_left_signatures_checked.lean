-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:54.697184+00:00
-- url     : https://prove2.me/submissions/e6fe8854-dcb1-40e6-bde9-efeda816b373

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared21.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared21.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared21
end
