-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:30.679259+00:00
-- url     : https://prove2.me/submissions/d06e1306-e75a-4b6d-b057-afac89cc2d04

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_008

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared26.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared26.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared26
end
