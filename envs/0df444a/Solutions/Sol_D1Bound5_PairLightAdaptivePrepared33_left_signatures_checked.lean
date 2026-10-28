-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:36.622968+00:00
-- url     : https://prove2.me/submissions/367e4ca7-438c-48d9-b9e4-e66f9ba5fd03

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared33.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared33.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared33
end
