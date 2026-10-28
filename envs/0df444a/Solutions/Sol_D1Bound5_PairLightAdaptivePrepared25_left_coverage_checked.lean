-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:38.888981+00:00
-- url     : https://prove2.me/submissions/b4166097-b833-4def-8e7a-8a636b1cea47

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared25.leftCached.map Prod.fst = PairLightPrepared25.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared25
end
