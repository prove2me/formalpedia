-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:45.52492+00:00
-- url     : https://prove2.me/submissions/0e70073a-9306-4130-aad1-bb78b8e2fed8

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared38.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared38.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared38
end
