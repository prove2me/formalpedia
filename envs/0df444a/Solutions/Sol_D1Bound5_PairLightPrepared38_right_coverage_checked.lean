-- Prove2me | solution 1 for D1Bound5.PairLightPrepared38.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:27.772692+00:00
-- url     : https://prove2.me/submissions/fbff2f28-38a2-4a0d-a66c-f9c535b433e9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared38.right_coverage_checked







end D1Bound5.PairLightPrepared38
end
