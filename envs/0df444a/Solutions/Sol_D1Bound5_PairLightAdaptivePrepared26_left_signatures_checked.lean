-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:47.488044+00:00
-- url     : https://prove2.me/submissions/d31e2c53-113e-40e4-8a2d-ddc20ed8c051

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared26.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared26.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared26
end
