-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:09.43608+00:00
-- url     : https://prove2.me/submissions/9ad181bb-650b-4239-bee5-019deff73dfa

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared33.leftCached.map Prod.fst = PairLightPrepared33.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared33
end
