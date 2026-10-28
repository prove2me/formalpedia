-- Prove2me | solution 1 for D1Bound5.PairLightPrepared33.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:17.7406+00:00
-- url     : https://prove2.me/submissions/daac3761-936b-45e7-bfc7-564fee4d1f2b

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared33.right_coverage_checked







end D1Bound5.PairLightPrepared33
end
