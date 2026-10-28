-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared20.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:23.011019+00:00
-- url     : https://prove2.me/submissions/fef27bb4-98e4-4861-8406-2bf0afc3fe36

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared20.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared20.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared20
end
