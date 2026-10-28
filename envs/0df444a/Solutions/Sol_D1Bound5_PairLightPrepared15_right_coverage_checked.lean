-- Prove2me | solution 1 for D1Bound5.PairLightPrepared15.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:21:32.174888+00:00
-- url     : https://prove2.me/submissions/7beb3ba3-2132-43ab-a472-ddaf8593c9a8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared15.right_coverage_checked







end D1Bound5.PairLightPrepared15
end
