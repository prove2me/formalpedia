-- Prove2me | solution 1 for D1Bound5.PairLightPrepared15.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:18:17.262992+00:00
-- url     : https://prove2.me/submissions/5a0a8525-ee86-4419-827e-581f88634ffb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared15.left_coverage_checked







end D1Bound5.PairLightPrepared15
end
