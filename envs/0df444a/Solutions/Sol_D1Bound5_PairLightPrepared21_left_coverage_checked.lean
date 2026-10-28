-- Prove2me | solution 1 for D1Bound5.PairLightPrepared21.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:14.699156+00:00
-- url     : https://prove2.me/submissions/ad975f24-4518-45ba-9e6a-9105165d8037

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared21.left_coverage_checked







end D1Bound5.PairLightPrepared21
end
