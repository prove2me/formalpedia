-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared13.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:39.849573+00:00
-- url     : https://prove2.me/submissions/493a47cf-1762-4eb3-9977-3333e8502593

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared13.leftCached.map Prod.fst = PairLightPrepared13.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared13
end
