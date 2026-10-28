-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:56:38.355674+00:00
-- url     : https://prove2.me/submissions/a6f3ff75-5517-450d-9c9b-62ede4b066f2

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared12.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared12.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared12
end
