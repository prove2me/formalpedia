-- Prove2me | solution 1 for D1Bound5.PairLightPrepared6.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:33:28.803718+00:00
-- url     : https://prove2.me/submissions/13c46436-3768-45c2-88f8-003b5ad79cce

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared6.right_coverage_checked







end D1Bound5.PairLightPrepared6
end
