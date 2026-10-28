-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:50:12.235801+00:00
-- url     : https://prove2.me/submissions/ef4f0587-410c-4170-aaff-9fdc1e97d89c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared33.rightCached.map Prod.fst = PairLightPrepared33.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared33
end
