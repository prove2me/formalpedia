-- Prove2me | solution 1 for D1Bound5.PairLightPrepared23.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:17.956642+00:00
-- url     : https://prove2.me/submissions/364086d0-7329-4d27-973f-df61deaf9751

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared23.left_coverage_checked







end D1Bound5.PairLightPrepared23
end
