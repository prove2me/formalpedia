-- Prove2me | solution 1 for D1Bound5.PairLightPrepared43.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:50.180585+00:00
-- url     : https://prove2.me/submissions/1e6b5928-7305-46ca-ab80-c052bf859c9c

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared43.right_signatures_checked





end D1Bound5.PairLightPrepared43
end
