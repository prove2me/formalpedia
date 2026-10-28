-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared2.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:26.726721+00:00
-- url     : https://prove2.me/submissions/7618feed-1e04-45e9-a26d-3b2b10c01cd6

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared2.leftCached.map Prod.fst = PairLightPrepared2.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared2
end
