-- Prove2me | solution 1 for D1Bound5.PairLightPrepared36.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:07.350144+00:00
-- url     : https://prove2.me/submissions/f3e0c662-7914-42b1-9da1-0e0d8676501e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared36.left_coverage_checked







end D1Bound5.PairLightPrepared36
end
