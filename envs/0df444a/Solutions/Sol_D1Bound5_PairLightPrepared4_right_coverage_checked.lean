-- Prove2me | solution 1 for D1Bound5.PairLightPrepared4.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:41:40.736+00:00
-- url     : https://prove2.me/submissions/711aa1e4-fd83-46f0-8380-4889624505a8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared4.right_coverage_checked







end D1Bound5.PairLightPrepared4
end
