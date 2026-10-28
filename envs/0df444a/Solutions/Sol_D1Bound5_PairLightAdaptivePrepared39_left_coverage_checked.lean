-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:22.955006+00:00
-- url     : https://prove2.me/submissions/0c942deb-fcf7-4801-8a6c-93616c49068f

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared39.leftCached.map Prod.fst = PairLightPrepared39.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared39
end
