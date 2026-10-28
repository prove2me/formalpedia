-- Prove2me | solution 1 for D1Bound5.PairLightPrepared44.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:30.257899+00:00
-- url     : https://prove2.me/submissions/3569b9e2-e442-4bd6-abdd-d6568857c84c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared44.left_coverage_checked







end D1Bound5.PairLightPrepared44
end
