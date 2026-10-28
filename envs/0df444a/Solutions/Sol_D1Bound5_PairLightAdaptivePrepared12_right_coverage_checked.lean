-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:43.174919+00:00
-- url     : https://prove2.me/submissions/ef097aaf-2017-4992-8de2-08aa83767a2c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    decide (PairLightPrepared12.rightCached.map Prod.fst = PairLightPrepared12.rightVertices) = true := by
  decide +kernel




end D1Bound5.PairLightAdaptivePrepared12
end
