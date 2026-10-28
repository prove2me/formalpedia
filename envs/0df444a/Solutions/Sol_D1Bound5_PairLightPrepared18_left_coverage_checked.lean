-- Prove2me | solution 1 for D1Bound5.PairLightPrepared18.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:22:54.915339+00:00
-- url     : https://prove2.me/submissions/ffdf8e7c-516b-4970-b72b-fe56b2e1456e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared18.left_coverage_checked







end D1Bound5.PairLightPrepared18
end
