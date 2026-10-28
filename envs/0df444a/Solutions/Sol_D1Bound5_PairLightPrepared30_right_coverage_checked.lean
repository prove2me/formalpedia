-- Prove2me | solution 1 for D1Bound5.PairLightPrepared30.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:22:55.71399+00:00
-- url     : https://prove2.me/submissions/80be3aa8-6dc6-4416-b51c-42e455eaaa2c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared30.right_coverage_checked







end D1Bound5.PairLightPrepared30
end
