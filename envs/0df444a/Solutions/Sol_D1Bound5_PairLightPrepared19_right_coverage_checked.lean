-- Prove2me | solution 1 for D1Bound5.PairLightPrepared19.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:55.607954+00:00
-- url     : https://prove2.me/submissions/4cf84a16-16f0-4d3f-a161-6452f24614dd

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared19.right_coverage_checked







end D1Bound5.PairLightPrepared19
end
