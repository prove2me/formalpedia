-- Prove2me | solution 1 for D1Bound5.PairLightPrepared47.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:06.4577+00:00
-- url     : https://prove2.me/submissions/594b0159-55e1-4544-b6cf-5f34b3d66937

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_002

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true := by
  decide +kernel





end D1Bound5.PairLightPrepared47
end
