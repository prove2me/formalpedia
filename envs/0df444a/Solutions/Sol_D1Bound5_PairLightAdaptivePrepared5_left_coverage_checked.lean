-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:45.12953+00:00
-- url     : https://prove2.me/submissions/56d0c152-ebc1-4166-b28c-3dac852d90d1

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared5.leftCached.map Prod.fst = PairLightPrepared5.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared5
end
