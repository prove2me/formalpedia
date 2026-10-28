-- Prove2me | solution 1 for D1Bound5.PairLightPrepared20.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:54.648282+00:00
-- url     : https://prove2.me/submissions/6e8d4337-f3bd-497e-acc8-eef386c44bf8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared20_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared20.right_coverage_checked







end D1Bound5.PairLightPrepared20
end
