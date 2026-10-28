-- Prove2me | solution 1 for D1Bound5.PairLightPrepared45.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:26.17051+00:00
-- url     : https://prove2.me/submissions/c02153e6-f915-4c67-853d-319027d0b39a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared45.left_coverage_checked







end D1Bound5.PairLightPrepared45
end
