-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:44.865843+00:00
-- url     : https://prove2.me/submissions/f8fec177-7b1c-4a8d-80d5-302228e63417

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared3.leftCached.map Prod.fst = PairLightPrepared3.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared3
end
