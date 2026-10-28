-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared42.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:11.172452+00:00
-- url     : https://prove2.me/submissions/2c9f84cd-50fc-4763-bbb9-d37703c59161

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared42.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared42.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared42
end
