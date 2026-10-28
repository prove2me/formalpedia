-- Prove2me | solution 1 for D1Bound5.PairLightPrepared47.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:01:15.25386+00:00
-- url     : https://prove2.me/submissions/af137a13-6d4d-491e-b750-00b5a6f9fadc

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_004

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true := by
  decide +kernel







end D1Bound5.PairLightPrepared47
end
