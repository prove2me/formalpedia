-- Prove2me | solution 1 for D1Bound5.PairLightPrepared23.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:39:44.940603+00:00
-- url     : https://prove2.me/submissions/a6e16498-9f3b-4e52-8e5e-c5af0da46c3f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared23.right_coverage_checked







end D1Bound5.PairLightPrepared23
end
