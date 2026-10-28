-- Prove2me | solution 1 for D1Bound5.PairLightPrepared6.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:52.139262+00:00
-- url     : https://prove2.me/submissions/58412e36-e967-42a6-9e88-724ddf407554

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared6.left_coverage_checked







end D1Bound5.PairLightPrepared6
end
