-- Prove2me | solution 1 for D1Bound5.PairLightPrepared35.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:26:21.526267+00:00
-- url     : https://prove2.me/submissions/d5ac5b60-8b1c-47db-b46d-839103c0ea97

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared35.left_coverage_checked







end D1Bound5.PairLightPrepared35
end
