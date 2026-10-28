-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:13.856917+00:00
-- url     : https://prove2.me/submissions/312b31ed-3970-4b3e-a865-b553c3d478cf

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared46.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared46.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared46
end
