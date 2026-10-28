-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:52.293089+00:00
-- url     : https://prove2.me/submissions/fb58cd36-6c66-4aad-a148-1ab5e6de560b

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared38.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared38.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared38
end
