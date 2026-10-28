-- Prove2me | solution 1 for D1Bound5.PairLightPrepared14.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:43.730991+00:00
-- url     : https://prove2.me/submissions/d36b5e9e-4f09-4586-987e-13c697c649ad

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared14.left_coverage_checked







end D1Bound5.PairLightPrepared14
end
