-- Prove2me | solution 1 for D1Bound5.PairLightPrepared14.right_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:21.744476+00:00
-- url     : https://prove2.me/submissions/f14021f3-7c59-4e37-ad6b-01e91072b1ca

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightVertices_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_coverage_checked

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (rightCached.map Prod.fst = rightVertices) = true :=
  PairLightAdaptivePrepared14.right_coverage_checked







end D1Bound5.PairLightPrepared14
end
