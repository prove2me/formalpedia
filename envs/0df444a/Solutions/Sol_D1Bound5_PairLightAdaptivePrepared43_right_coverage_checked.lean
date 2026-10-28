-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:23.731477+00:00
-- url     : https://prove2.me/submissions/a0ce5257-4b5a-4a5a-864b-b2942a55cc8b

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared43.rightCached.map Prod.fst = PairLightPrepared43.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared43
end
