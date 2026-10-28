-- Prove2me | solution 1 for D1Bound5.PairLightPrepared1.left_coverage_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:10.424709+00:00
-- url     : https://prove2.me/submissions/ea08e0ec-fd8f-4092-afca-fc4101e5bb19

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_left_coverage_checked

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.solution :
    decide (leftCached.map Prod.fst = leftVertices) = true :=
  PairLightAdaptivePrepared1.left_coverage_checked







end D1Bound5.PairLightPrepared1
end
