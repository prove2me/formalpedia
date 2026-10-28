-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:42.961403+00:00
-- url     : https://prove2.me/submissions/929d8009-77e4-4503-80b4-231f5f5d2c8e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared18.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared18.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared18
end
