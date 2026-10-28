-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:39:50.828354+00:00
-- url     : https://prove2.me/submissions/e8f8ef14-2231-482d-8725-0df556b9eb7e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared7.leftCached.map Prod.fst = PairLightPrepared7.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared7
end
