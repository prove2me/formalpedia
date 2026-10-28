-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:53.645964+00:00
-- url     : https://prove2.me/submissions/96faa9cd-85f7-40b7-9667-e92bc93f9123

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared46.leftCached.map Prod.fst = PairLightPrepared46.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared46
end
