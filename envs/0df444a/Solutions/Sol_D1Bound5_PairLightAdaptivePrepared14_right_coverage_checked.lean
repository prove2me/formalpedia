-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:52.170009+00:00
-- url     : https://prove2.me/submissions/51af17e9-1cae-480f-9d4c-389877fad1cc

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared14.rightCached.map Prod.fst = PairLightPrepared14.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared14
end
