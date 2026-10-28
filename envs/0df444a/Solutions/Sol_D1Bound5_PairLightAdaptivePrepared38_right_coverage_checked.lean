-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:27.996709+00:00
-- url     : https://prove2.me/submissions/6d76768e-db37-4c2a-928b-5323fe80709c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared38.rightCached.map Prod.fst = PairLightPrepared38.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared38
end
