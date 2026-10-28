-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:47.654897+00:00
-- url     : https://prove2.me/submissions/6a4cc2be-c31d-4deb-aa35-76aba875b678

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared25.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared25.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared25
end
