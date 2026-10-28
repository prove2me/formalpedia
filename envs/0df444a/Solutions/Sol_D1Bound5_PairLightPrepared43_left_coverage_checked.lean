-- Prove2me | solution 1 for D1Bound5.PairLightPrepared43.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:09.535966+00:00
-- url     : https://prove2.me/submissions/c857b7e2-8c46-4f78-b4e4-247dc2fa3974

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared43.left_coverage_checked







end D1Bound5.PairLightPrepared43
end
