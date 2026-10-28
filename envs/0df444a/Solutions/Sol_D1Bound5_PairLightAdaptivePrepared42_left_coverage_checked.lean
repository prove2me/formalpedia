-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared42.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:32.514213+00:00
-- url     : https://prove2.me/submissions/78cea9e3-149e-4ee7-9261-1dbfe635ec03

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared42.leftCached.map Prod.fst = PairLightPrepared42.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared42
end
