-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:14.777114+00:00
-- url     : https://prove2.me/submissions/8013a724-2e42-4480-abd7-bdcbfa0b7dd2

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared24.leftCached.map Prod.fst = PairLightPrepared24.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared24
end
