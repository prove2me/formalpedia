-- Prove2me | solution 1 for D1Bound5.PairLightPrepared12.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:23.547311+00:00
-- url     : https://prove2.me/submissions/816c548c-900b-4ed3-bfb3-ea4bc66f5e75

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared12.right_coverage_checked







end D1Bound5.PairLightPrepared12
end
