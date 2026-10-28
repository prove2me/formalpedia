-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:45.594594+00:00
-- url     : https://prove2.me/submissions/cb50e991-530c-477d-8d36-227b951b7cb6

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared35.rightCached.map Prod.fst = PairLightPrepared35.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared35
end
