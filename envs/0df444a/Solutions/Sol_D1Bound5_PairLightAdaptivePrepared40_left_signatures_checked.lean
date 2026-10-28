-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:22:11.877287+00:00
-- url     : https://prove2.me/submissions/176c7951-cd9d-43b8-98b5-6c7a7959d170

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared40.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared40.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared40
end
