-- Prove2me | solution 1 for D1Bound5.PairLightPrepared30.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:40.754153+00:00
-- url     : https://prove2.me/submissions/edf8124a-fb2e-4d4b-89cf-ec8c8b765495

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared30_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared30.left_coverage_checked







end D1Bound5.PairLightPrepared30
end
