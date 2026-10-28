-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:19.143934+00:00
-- url     : https://prove2.me/submissions/46f7ab0f-852d-4f02-a479-4b05c78d27ba

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared7.rightCached.map Prod.fst = PairLightPrepared7.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared7
end
