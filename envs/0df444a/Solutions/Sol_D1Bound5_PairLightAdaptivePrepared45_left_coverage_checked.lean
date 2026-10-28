-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared45.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:41:56.586346+00:00
-- url     : https://prove2.me/submissions/255f36ab-f804-4841-aa9c-8b9cb5e1df17

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared45.leftCached.map Prod.fst = PairLightPrepared45.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared45
end
