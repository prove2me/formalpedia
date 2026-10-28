-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:19:47.279605+00:00
-- url     : https://prove2.me/submissions/16f42c12-d6f7-4355-b5e3-9982ea418079

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared48.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared48.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared48
end
