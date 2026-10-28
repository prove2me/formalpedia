-- Prove2me | solution 1 for D1Bound5.PairLightPrepared9.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:11.962952+00:00
-- url     : https://prove2.me/submissions/83f5aff6-7a78-48d6-9a77-3ef28936be11

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared9.right_coverage_checked







end D1Bound5.PairLightPrepared9
end
