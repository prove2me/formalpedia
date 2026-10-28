-- Prove2me | solution 1 for D1Bound5.PairLightPrepared39.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:26:19.886574+00:00
-- url     : https://prove2.me/submissions/4bc5919a-aec8-4131-9d26-92fb8f0f45db

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared39.left_coverage_checked







end D1Bound5.PairLightPrepared39
end
