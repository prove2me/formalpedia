-- Prove2me | solution 1 for D1Bound5.PairLightPrepared10.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:15.435698+00:00
-- url     : https://prove2.me/submissions/1981eb35-ed2d-420c-bd0c-b0b6ad7c00cd

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared10.left_coverage_checked







end D1Bound5.PairLightPrepared10
end
