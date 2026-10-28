-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared20.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:56.85929+00:00
-- url     : https://prove2.me/submissions/1c17f262-960d-4cc2-9ba7-9ba739457430

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared20.rightCached.map Prod.fst = PairLightPrepared20.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared20
end
