-- Prove2me | solution 1 for D1Bound5.PairLightPrepared24.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:20.951673+00:00
-- url     : https://prove2.me/submissions/2c301275-0e58-4df9-a596-eeef0a7d2574

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared24.right_coverage_checked







end D1Bound5.PairLightPrepared24
end
