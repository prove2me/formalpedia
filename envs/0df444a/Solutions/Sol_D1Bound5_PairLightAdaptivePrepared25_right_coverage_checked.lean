-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:32.062959+00:00
-- url     : https://prove2.me/submissions/115e6f22-1f3f-4047-8dca-f61b12fa37d6

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared25.rightCached.map Prod.fst = PairLightPrepared25.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared25
end
