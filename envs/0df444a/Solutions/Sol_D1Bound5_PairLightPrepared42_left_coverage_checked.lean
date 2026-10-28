-- Prove2me | solution 1 for D1Bound5.PairLightPrepared42.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:11.331953+00:00
-- url     : https://prove2.me/submissions/b390f710-be7b-4714-af89-28a2a1832828

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared42_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared42.left_coverage_checked







end D1Bound5.PairLightPrepared42
end
