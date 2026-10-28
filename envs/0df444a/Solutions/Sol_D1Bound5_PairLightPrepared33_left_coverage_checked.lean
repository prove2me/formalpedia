-- Prove2me | solution 1 for D1Bound5.PairLightPrepared33.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:10.362129+00:00
-- url     : https://prove2.me/submissions/6b4c7d86-b71f-4d83-adfc-d991c5514c2e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared33.left_coverage_checked







end D1Bound5.PairLightPrepared33
end
