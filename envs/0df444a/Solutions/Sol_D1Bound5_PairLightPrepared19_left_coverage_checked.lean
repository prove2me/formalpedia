-- Prove2me | solution 1 for D1Bound5.PairLightPrepared19.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:19:22.041754+00:00
-- url     : https://prove2.me/submissions/fd907e8c-8f98-49b4-91d0-267114b3dc7a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared19.left_coverage_checked







end D1Bound5.PairLightPrepared19
end
