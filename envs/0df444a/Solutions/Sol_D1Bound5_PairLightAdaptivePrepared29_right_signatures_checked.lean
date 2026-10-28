-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:22:59.655981+00:00
-- url     : https://prove2.me/submissions/72498b34-4702-4155-930d-deda84583ea6

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared29.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared29.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared29
end
