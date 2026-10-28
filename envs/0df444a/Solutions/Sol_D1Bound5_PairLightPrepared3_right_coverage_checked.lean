-- Prove2me | solution 1 for D1Bound5.PairLightPrepared3.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:21.948979+00:00
-- url     : https://prove2.me/submissions/6aba6eac-aeb8-4f33-8ab8-0dc377beaab0

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared3.right_coverage_checked







end D1Bound5.PairLightPrepared3
end
