-- Prove2me | solution 1 for D1Bound5.PairLightPrepared46.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:28.625705+00:00
-- url     : https://prove2.me/submissions/a81a7cc9-0410-4ad4-9347-c4b7f31d9a57

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared46.right_coverage_checked







end D1Bound5.PairLightPrepared46
end
