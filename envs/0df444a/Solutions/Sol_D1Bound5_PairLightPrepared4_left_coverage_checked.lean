-- Prove2me | solution 1 for D1Bound5.PairLightPrepared4.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:31:00.093536+00:00
-- url     : https://prove2.me/submissions/929deb0e-5c14-4ff7-8748-1a4640e88423

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared4_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared4.left_coverage_checked







end D1Bound5.PairLightPrepared4
end
