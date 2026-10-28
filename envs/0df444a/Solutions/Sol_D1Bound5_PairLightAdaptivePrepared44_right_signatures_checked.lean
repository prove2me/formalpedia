-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared44.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:05.879201+00:00
-- url     : https://prove2.me/submissions/a437b469-cd9f-4a2c-b091-16571478dff8

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared44.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared44.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared44
end
