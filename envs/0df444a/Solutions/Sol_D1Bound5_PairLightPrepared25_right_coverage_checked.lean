-- Prove2me | solution 1 for D1Bound5.PairLightPrepared25.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:33:26.379489+00:00
-- url     : https://prove2.me/submissions/eb9f0bc2-5e2e-4aef-976e-1c1877a20b4c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared25.right_coverage_checked







end D1Bound5.PairLightPrepared25
end
