-- Prove2me | solution 1 for D1Bound5.PairLightPrepared13.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:48.334895+00:00
-- url     : https://prove2.me/submissions/309ade4b-b07d-433a-95e9-7b59f4579b7a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared13_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared13.right_signatures_checked





end D1Bound5.PairLightPrepared13
end
