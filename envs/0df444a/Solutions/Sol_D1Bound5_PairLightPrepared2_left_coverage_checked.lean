-- Prove2me | solution 1 for D1Bound5.PairLightPrepared2.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:27.095262+00:00
-- url     : https://prove2.me/submissions/2b99f7bc-898a-4bbc-84c0-5f7058022255

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared2.left_coverage_checked







end D1Bound5.PairLightPrepared2
end
