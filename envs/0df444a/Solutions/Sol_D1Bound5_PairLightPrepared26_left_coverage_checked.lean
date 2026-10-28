-- Prove2me | solution 1 for D1Bound5.PairLightPrepared26.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:10.9206+00:00
-- url     : https://prove2.me/submissions/9298e703-f4d9-44ed-8ca5-bb5e17a93bb7

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared26.left_coverage_checked







end D1Bound5.PairLightPrepared26
end
