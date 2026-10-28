-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:37.318816+00:00
-- url     : https://prove2.me/submissions/8abb9a02-a926-4d0e-bcde-348394b658aa

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared48.leftCached.map Prod.fst = PairLightPrepared48.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared48
end
