-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:12.736229+00:00
-- url     : https://prove2.me/submissions/dda4110d-1e6e-4860-beab-eabf8e2e92e8

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftVertices_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (PairLightPrepared21.leftCached.map Prod.fst = PairLightPrepared21.leftVertices) = true := by
  decide +kernel








end D1Bound5.PairLightAdaptivePrepared21
end
