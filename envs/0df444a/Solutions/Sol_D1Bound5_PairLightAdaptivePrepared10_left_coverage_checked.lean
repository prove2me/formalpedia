-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:24.453305+00:00
-- url     : https://prove2.me/submissions/cfd720cf-8ff4-4faf-9488-2d1b8a32994b

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared10.leftCached.map Prod.fst = PairLightPrepared10.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared10
end
