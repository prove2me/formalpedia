-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:13:42.859965+00:00
-- url     : https://prove2.me/submissions/216bf0e7-0aa5-4d90-9a5b-b9fe344f80aa

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared48.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared48.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared48
end
