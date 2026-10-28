-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:23.028603+00:00
-- url     : https://prove2.me/submissions/61a3bdd9-975c-49dc-b0d6-893ca2034511

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared30.leftCached.map Prod.fst = PairLightPrepared30.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared30
end
