-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared9.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:22.947019+00:00
-- url     : https://prove2.me/submissions/42bd2c59-d656-4b10-9169-12191a053b77

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared9.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared9.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared9
end
