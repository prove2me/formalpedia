-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:45.086574+00:00
-- url     : https://prove2.me/submissions/b6d30be2-5a0b-4fe1-a7ce-a9e339f232c3

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared18.leftCached.map Prod.fst = PairLightPrepared18.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared18
end
