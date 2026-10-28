-- Prove2me | solution 1 for D1Bound5.PairLightPrepared40.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:24:27.754585+00:00
-- url     : https://prove2.me/submissions/86b2ff47-6ff0-40c6-a445-4a93f30661b6

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared40.left_coverage_checked







end D1Bound5.PairLightPrepared40
end
