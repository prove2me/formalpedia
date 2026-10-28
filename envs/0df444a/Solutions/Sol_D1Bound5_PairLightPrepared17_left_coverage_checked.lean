-- Prove2me | solution 1 for D1Bound5.PairLightPrepared17.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:26:19.069711+00:00
-- url     : https://prove2.me/submissions/93fa4709-174f-4b6c-936c-3be414d3b5ec

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared17.left_coverage_checked







end D1Bound5.PairLightPrepared17
end
