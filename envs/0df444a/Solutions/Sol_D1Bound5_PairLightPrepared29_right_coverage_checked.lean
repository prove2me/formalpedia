-- Prove2me | solution 1 for D1Bound5.PairLightPrepared29.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:21:31.279845+00:00
-- url     : https://prove2.me/submissions/f91c3731-2cae-48ca-9a6c-f2bbed980213

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared29.right_coverage_checked







end D1Bound5.PairLightPrepared29
end
