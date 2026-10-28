-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared9.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:24.014027+00:00
-- url     : https://prove2.me/submissions/b1167429-3720-41f1-9614-1234c8eb5e3c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared9.rightCached.map Prod.fst = PairLightPrepared9.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared9
end
