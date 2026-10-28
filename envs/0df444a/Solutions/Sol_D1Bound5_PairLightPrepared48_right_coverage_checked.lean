-- Prove2me | solution 1 for D1Bound5.PairLightPrepared48.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:00.391118+00:00
-- url     : https://prove2.me/submissions/bb7a5517-d1bb-484c-8a90-3e01dd02a531

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared48.right_coverage_checked







end D1Bound5.PairLightPrepared48
end
