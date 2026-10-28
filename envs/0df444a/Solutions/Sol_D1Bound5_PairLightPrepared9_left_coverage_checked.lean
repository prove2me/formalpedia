-- Prove2me | solution 1 for D1Bound5.PairLightPrepared9.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:34:50.897923+00:00
-- url     : https://prove2.me/submissions/9187c95b-6339-4316-8385-aadb446b0d59

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared9.left_coverage_checked







end D1Bound5.PairLightPrepared9
end
