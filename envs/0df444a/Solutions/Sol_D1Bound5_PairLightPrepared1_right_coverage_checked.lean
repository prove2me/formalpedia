-- Prove2me | solution 1 for D1Bound5.PairLightPrepared1.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:15.532875+00:00
-- url     : https://prove2.me/submissions/50074174-1244-4fa0-b724-90c5c74e54cb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared1.right_coverage_checked







end D1Bound5.PairLightPrepared1
end
