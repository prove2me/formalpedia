-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:48:34.383531+00:00
-- url     : https://prove2.me/submissions/cb916588-31d8-4b21-a737-e201f1f53201

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared12.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared12.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared12
end
