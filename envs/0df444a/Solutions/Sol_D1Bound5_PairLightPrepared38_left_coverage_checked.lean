-- Prove2me | solution 1 for D1Bound5.PairLightPrepared38.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:18.826748+00:00
-- url     : https://prove2.me/submissions/bee21adf-e3a0-46c1-9b8f-702c5e64e06d

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared38.left_coverage_checked







end D1Bound5.PairLightPrepared38
end
