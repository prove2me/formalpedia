-- Prove2me | solution 1 for D1Bound5.PairLightPrepared26.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:18:17.975716+00:00
-- url     : https://prove2.me/submissions/b3a18b7a-7ff4-4110-94c2-6d03dfe86636

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_008
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared26.right_coverage_checked







end D1Bound5.PairLightPrepared26
end
