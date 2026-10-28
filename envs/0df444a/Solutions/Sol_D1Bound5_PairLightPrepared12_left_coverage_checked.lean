-- Prove2me | solution 1 for D1Bound5.PairLightPrepared12.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:21.075601+00:00
-- url     : https://prove2.me/submissions/aa04711c-a29c-479d-95b4-e935b0af675b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared12.left_coverage_checked







end D1Bound5.PairLightPrepared12
end
