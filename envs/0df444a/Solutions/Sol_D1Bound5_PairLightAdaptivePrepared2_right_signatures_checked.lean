-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared2.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:46:02.764183+00:00
-- url     : https://prove2.me/submissions/25b67a36-eab3-45d6-bd29-10c327dcd795

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared2.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared2.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared2
end
