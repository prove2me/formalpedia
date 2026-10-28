-- Prove2me | solution 1 for D1Bound5.PairLightPrepared40.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:13.620439+00:00
-- url     : https://prove2.me/submissions/705f7cbb-740e-4ba5-882a-fb734dc82c86

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared40.right_coverage_checked







end D1Bound5.PairLightPrepared40
end
