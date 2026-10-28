-- Prove2me | solution 1 for D1Bound5.PairLightPrepared48.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:22:58.132622+00:00
-- url     : https://prove2.me/submissions/34fc2b8e-36e4-4fc5-875b-eac5ac38112c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared48.left_coverage_checked







end D1Bound5.PairLightPrepared48
end
