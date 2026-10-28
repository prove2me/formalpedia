-- Prove2me | solution 1 for D1Bound5.PairLightPrepared24.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:06.501989+00:00
-- url     : https://prove2.me/submissions/8c7db131-d821-494d-ba63-fe11857c4b2d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared24.left_coverage_checked







end D1Bound5.PairLightPrepared24
end
