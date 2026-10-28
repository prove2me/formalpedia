-- Prove2me | solution 1 for D1Bound5.PairLightPrepared25.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:56.500206+00:00
-- url     : https://prove2.me/submissions/f94e0f08-11d6-491a-b2e1-ad8d8daa2684

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared25.left_coverage_checked







end D1Bound5.PairLightPrepared25
end
