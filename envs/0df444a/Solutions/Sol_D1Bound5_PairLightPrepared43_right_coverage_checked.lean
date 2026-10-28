-- Prove2me | solution 1 for D1Bound5.PairLightPrepared43.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:59.153402+00:00
-- url     : https://prove2.me/submissions/acc19a01-aec6-493a-a574-103ca3f0e481

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared43.right_coverage_checked







end D1Bound5.PairLightPrepared43
end
