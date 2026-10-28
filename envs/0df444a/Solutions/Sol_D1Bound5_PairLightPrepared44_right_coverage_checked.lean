-- Prove2me | solution 1 for D1Bound5.PairLightPrepared44.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:13.843527+00:00
-- url     : https://prove2.me/submissions/41585cb2-c058-4f2a-85a0-584fb66f268e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_003
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared44.right_coverage_checked







end D1Bound5.PairLightPrepared44
end
