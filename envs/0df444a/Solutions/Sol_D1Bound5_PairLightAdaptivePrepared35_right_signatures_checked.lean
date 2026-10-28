-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:34:40.088516+00:00
-- url     : https://prove2.me/submissions/5d2b949f-f971-4248-8fce-3cfafdbc0e71

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared35.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared35.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared35
end
