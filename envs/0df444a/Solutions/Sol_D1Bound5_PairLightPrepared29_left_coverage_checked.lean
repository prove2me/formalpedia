-- Prove2me | solution 1 for D1Bound5.PairLightPrepared29.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:14:58.521102+00:00
-- url     : https://prove2.me/submissions/69e354d2-21ca-4790-b3da-e48c6e826e70

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared29.left_coverage_checked







end D1Bound5.PairLightPrepared29
end
