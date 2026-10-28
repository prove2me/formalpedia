-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:04.7424+00:00
-- url     : https://prove2.me/submissions/799a5b07-b733-4c1f-8da4-b07b07550e01

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared17.leftCached.map Prod.fst = PairLightPrepared17.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared17
end
