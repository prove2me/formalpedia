-- Prove2me | solution 1 for D1Bound5.PairLightPrepared28.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:10.063257+00:00
-- url     : https://prove2.me/submissions/6e0b588c-03ce-43fa-9ff5-66e55a1a4676

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared28.right_coverage_checked







end D1Bound5.PairLightPrepared28
end
