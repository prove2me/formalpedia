-- Prove2me | solution 1 for D1Bound5.PairLightPrepared13.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:53.791369+00:00
-- url     : https://prove2.me/submissions/dc8d375f-3f21-42b6-bf32-257ff8e973a6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared13_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared13.left_coverage_checked







end D1Bound5.PairLightPrepared13
end
