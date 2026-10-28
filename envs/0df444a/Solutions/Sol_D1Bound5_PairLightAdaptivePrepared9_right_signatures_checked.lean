-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared9.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:25.770992+00:00
-- url     : https://prove2.me/submissions/b8a8064a-0c28-44af-9b06-d940e56a7665

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared9.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared9.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared9
end
