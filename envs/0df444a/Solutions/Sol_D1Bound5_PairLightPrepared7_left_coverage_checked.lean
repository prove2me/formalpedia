-- Prove2me | solution 1 for D1Bound5.PairLightPrepared7.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:34:34.954334+00:00
-- url     : https://prove2.me/submissions/ea94b539-bd78-45a4-80dd-8e207b19e301

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared7.left_coverage_checked







end D1Bound5.PairLightPrepared7
end
