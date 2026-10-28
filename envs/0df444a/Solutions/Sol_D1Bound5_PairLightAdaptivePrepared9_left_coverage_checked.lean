-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared9.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:04.604924+00:00
-- url     : https://prove2.me/submissions/53b1ccaf-6f0f-4207-b0a3-c09f325ba209

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared9.leftCached.map Prod.fst = PairLightPrepared9.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared9
end
