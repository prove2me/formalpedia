-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:12.048971+00:00
-- url     : https://prove2.me/submissions/1e571e24-5a28-472c-b3c0-7da4e0e87f64

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared33.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared33.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared33
end
