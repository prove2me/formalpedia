-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:32.643871+00:00
-- url     : https://prove2.me/submissions/36484d6f-48e8-4f64-b3df-de77e525fc8e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared18.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared18.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared18
end
