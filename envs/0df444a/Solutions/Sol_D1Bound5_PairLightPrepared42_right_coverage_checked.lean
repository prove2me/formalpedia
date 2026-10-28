-- Prove2me | solution 1 for D1Bound5.PairLightPrepared42.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:08.766167+00:00
-- url     : https://prove2.me/submissions/2eeddc9e-30d3-4309-8a7e-807da0578ee1

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared42_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared42.right_coverage_checked







end D1Bound5.PairLightPrepared42
end
