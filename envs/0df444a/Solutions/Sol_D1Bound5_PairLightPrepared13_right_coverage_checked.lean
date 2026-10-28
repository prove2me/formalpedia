-- Prove2me | solution 1 for D1Bound5.PairLightPrepared13.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:49.285294+00:00
-- url     : https://prove2.me/submissions/5246a315-6858-40f7-9c99-f1889ef35f34

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared13_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared13.right_coverage_checked







end D1Bound5.PairLightPrepared13
end
