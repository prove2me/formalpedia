-- Prove2me | solution 1 for D1Bound5.PairLightPrepared10.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:40:40.909991+00:00
-- url     : https://prove2.me/submissions/ad70d247-308b-4ae3-bd1b-f0679992e612

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared10.right_coverage_checked







end D1Bound5.PairLightPrepared10
end
