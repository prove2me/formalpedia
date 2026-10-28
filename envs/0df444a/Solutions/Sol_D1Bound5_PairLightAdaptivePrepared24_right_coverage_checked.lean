-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:33.415346+00:00
-- url     : https://prove2.me/submissions/da336a85-8610-4a45-90e4-ea529bb1950d

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared24.rightCached.map Prod.fst = PairLightPrepared24.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared24
end
