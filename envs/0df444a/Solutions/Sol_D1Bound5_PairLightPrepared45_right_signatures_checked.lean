-- Prove2me | solution 1 for D1Bound5.PairLightPrepared45.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:23.627521+00:00
-- url     : https://prove2.me/submissions/c5f3ead1-7401-4030-8997-44ed24048ead

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared45.right_signatures_checked





end D1Bound5.PairLightPrepared45
end
