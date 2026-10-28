-- Prove2me | solution 1 for D1Bound5.PairLightPrepared39.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:38:51.590102+00:00
-- url     : https://prove2.me/submissions/a5b41864-6c74-4f9e-8317-44b284f11c7a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared39.right_coverage_checked







end D1Bound5.PairLightPrepared39
end
