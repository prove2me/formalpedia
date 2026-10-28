-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:56.809491+00:00
-- url     : https://prove2.me/submissions/fae30c29-7aa9-4254-889c-7875b785f819

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared40.leftCached.map Prod.fst = PairLightPrepared40.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared40
end
