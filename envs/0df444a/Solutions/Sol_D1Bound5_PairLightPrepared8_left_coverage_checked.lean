-- Prove2me | solution 1 for D1Bound5.PairLightPrepared8.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:36:33.359765+00:00
-- url     : https://prove2.me/submissions/157b0aae-e817-4048-bea8-58c64b084772

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared8.left_coverage_checked







end D1Bound5.PairLightPrepared8
end
