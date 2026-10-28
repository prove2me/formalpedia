-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:33.359792+00:00
-- url     : https://prove2.me/submissions/d51ac4a4-2bcc-4c98-90d9-ab162742b1c3

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared43.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared43.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared43
end
