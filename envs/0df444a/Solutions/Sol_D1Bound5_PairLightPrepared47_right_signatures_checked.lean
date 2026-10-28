-- Prove2me | solution 1 for D1Bound5.PairLightPrepared47.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:00.245391+00:00
-- url     : https://prove2.me/submissions/5409ccb4-4200-422d-85d2-9d4134ce0d53

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_004

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by
  decide +kernel





end D1Bound5.PairLightPrepared47
end
