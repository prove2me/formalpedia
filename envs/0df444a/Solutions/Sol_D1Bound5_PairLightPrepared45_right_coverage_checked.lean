-- Prove2me | solution 1 for D1Bound5.PairLightPrepared45.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:14:56.850458+00:00
-- url     : https://prove2.me/submissions/9b694a86-1ea8-4595-b8a9-835880284dc9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared45.right_coverage_checked







end D1Bound5.PairLightPrepared45
end
