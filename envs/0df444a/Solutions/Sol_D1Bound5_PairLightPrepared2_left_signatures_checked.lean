-- Prove2me | solution 1 for D1Bound5.PairLightPrepared2.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:20.294272+00:00
-- url     : https://prove2.me/submissions/33688621-eb24-4b63-8914-e9f237251cd8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared2_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared2.left_signatures_checked





end D1Bound5.PairLightPrepared2
end
