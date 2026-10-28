-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:06.51818+00:00
-- url     : https://prove2.me/submissions/871e1919-a48a-4c1b-9195-9621dfd3e139

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_008

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared26.rightCached.map Prod.fst = PairLightPrepared26.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared26
end
