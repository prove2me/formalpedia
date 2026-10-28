-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:17.139655+00:00
-- url     : https://prove2.me/submissions/c4e18279-4fdc-4c32-81e1-b6fdbad3e336

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared11.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared11.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared11
end
