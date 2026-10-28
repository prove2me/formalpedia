-- Prove2me | solution 1 for D1Bound5.PairLightPrepared35.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:24:28.566223+00:00
-- url     : https://prove2.me/submissions/66639dd8-838e-4d3f-91b0-c562e0934a08

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared35.right_coverage_checked







end D1Bound5.PairLightPrepared35
end
