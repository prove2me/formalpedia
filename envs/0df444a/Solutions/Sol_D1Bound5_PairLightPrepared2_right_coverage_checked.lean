-- Prove2me | solution 1 for D1Bound5.PairLightPrepared2.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:34:34.136639+00:00
-- url     : https://prove2.me/submissions/a899319f-81fd-489d-af00-2aa56f8026f8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared2.right_coverage_checked







end D1Bound5.PairLightPrepared2
end
