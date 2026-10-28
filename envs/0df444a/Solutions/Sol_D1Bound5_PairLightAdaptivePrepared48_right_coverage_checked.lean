-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:31.564611+00:00
-- url     : https://prove2.me/submissions/da4964b5-4384-4cec-9376-27a0a7af7ca9

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared48.rightCached.map Prod.fst = PairLightPrepared48.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared48
end
