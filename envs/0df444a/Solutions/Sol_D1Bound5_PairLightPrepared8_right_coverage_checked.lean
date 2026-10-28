-- Prove2me | solution 1 for D1Bound5.PairLightPrepared8.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:05.605006+00:00
-- url     : https://prove2.me/submissions/93a1eca8-d6b3-4bba-b7f1-e73adafecde7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared8.right_coverage_checked







end D1Bound5.PairLightPrepared8
end
