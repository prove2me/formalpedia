-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared42.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:44.139248+00:00
-- url     : https://prove2.me/submissions/8ad87dc3-0b06-4e2f-aafc-1689e88fcc06

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared42.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared42.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared42
end
