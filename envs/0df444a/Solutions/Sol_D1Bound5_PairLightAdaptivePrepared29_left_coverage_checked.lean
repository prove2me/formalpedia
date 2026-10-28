-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:23.880327+00:00
-- url     : https://prove2.me/submissions/e0bc259e-1bdd-4c04-8a7b-3e793faf5ee9

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared29.leftCached.map Prod.fst = PairLightPrepared29.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared29
end
