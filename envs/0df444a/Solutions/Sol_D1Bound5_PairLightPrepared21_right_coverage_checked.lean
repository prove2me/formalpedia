-- Prove2me | solution 1 for D1Bound5.PairLightPrepared21.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:29:26.314596+00:00
-- url     : https://prove2.me/submissions/3184f80e-39b7-4272-8f39-4a33f899c83b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared21.right_coverage_checked







end D1Bound5.PairLightPrepared21
end
