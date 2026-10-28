-- Prove2me | solution 1 for D1Bound5.PairLightPrepared3.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:02.317081+00:00
-- url     : https://prove2.me/submissions/d9095ad5-3817-4895-acac-262798ebd4c7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared3.left_coverage_checked







end D1Bound5.PairLightPrepared3
end
