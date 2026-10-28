-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:37.862849+00:00
-- url     : https://prove2.me/submissions/4e3eae55-ffc5-472e-a248-eedb287e254f

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared38.leftCached.map Prod.fst = PairLightPrepared38.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared38
end
