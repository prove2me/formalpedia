-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared2.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:53.908735+00:00
-- url     : https://prove2.me/submissions/1814bb9d-1c17-4241-b500-b65533a54b09

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared2.rightCached.map Prod.fst = PairLightPrepared2.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared2
end
