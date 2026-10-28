-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared13.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:21.787772+00:00
-- url     : https://prove2.me/submissions/5d6d88b5-b15f-444e-9017-27d12ccd5640

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared13.rightCached.map Prod.fst = PairLightPrepared13.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared13
end
