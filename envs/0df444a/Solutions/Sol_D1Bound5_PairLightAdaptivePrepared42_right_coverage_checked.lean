-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared42.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:00.669298+00:00
-- url     : https://prove2.me/submissions/8fcc1caa-6f8b-4040-b883-e3cebee99598

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared42.rightCached.map Prod.fst = PairLightPrepared42.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared42
end
