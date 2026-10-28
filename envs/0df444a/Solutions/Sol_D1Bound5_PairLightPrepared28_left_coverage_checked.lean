-- Prove2me | solution 1 for D1Bound5.PairLightPrepared28.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:45.317913+00:00
-- url     : https://prove2.me/submissions/0c2705ed-d1c3-4f13-84eb-4477079a447a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared28.left_coverage_checked







end D1Bound5.PairLightPrepared28
end
