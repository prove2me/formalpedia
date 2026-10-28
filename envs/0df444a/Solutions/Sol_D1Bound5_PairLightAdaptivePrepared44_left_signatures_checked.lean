-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared44.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:56.949664+00:00
-- url     : https://prove2.me/submissions/65651f77-6881-4c43-85cc-2a00ff451df0

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared44.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared44.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared44
end
