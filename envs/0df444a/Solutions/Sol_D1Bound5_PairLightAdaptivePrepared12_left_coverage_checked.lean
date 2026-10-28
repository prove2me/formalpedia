-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:08.459488+00:00
-- url     : https://prove2.me/submissions/34661ce4-9de0-4eb8-a7ef-bd1faf9ec043

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared12.leftCached.map Prod.fst = PairLightPrepared12.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared12
end
