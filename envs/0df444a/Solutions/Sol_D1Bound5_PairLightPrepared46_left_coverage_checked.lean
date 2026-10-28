-- Prove2me | solution 1 for D1Bound5.PairLightPrepared46.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:48.810511+00:00
-- url     : https://prove2.me/submissions/90addf8b-cb8a-4a25-a842-7ceebfa6d352

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared46.left_coverage_checked







end D1Bound5.PairLightPrepared46
end
