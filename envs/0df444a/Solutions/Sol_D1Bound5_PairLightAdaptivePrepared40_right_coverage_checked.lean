-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:18.076232+00:00
-- url     : https://prove2.me/submissions/4977f591-3740-40d9-95ca-5a75d5e6522a

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared40.rightCached.map Prod.fst = PairLightPrepared40.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared40
end
