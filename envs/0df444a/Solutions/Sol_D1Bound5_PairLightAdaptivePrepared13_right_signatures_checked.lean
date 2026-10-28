-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared13.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:53.344705+00:00
-- url     : https://prove2.me/submissions/e3b9274a-d9f0-4cc3-8e53-dbfb0cf86161

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared13.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared13.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared13
end
