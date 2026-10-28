-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:47.704797+00:00
-- url     : https://prove2.me/submissions/8651df20-ae95-4418-992f-e917d520edb1

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared19.leftCached.map Prod.fst = PairLightPrepared19.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared19
end
