-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:33.012588+00:00
-- url     : https://prove2.me/submissions/ebc0f3c8-e9be-41c1-99f6-5677ca07ea56

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared30.rightCached.map Prod.fst = PairLightPrepared30.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared30
end
