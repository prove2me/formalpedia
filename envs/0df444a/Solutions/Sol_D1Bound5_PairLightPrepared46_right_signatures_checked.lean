-- Prove2me | solution 1 for D1Bound5.PairLightPrepared46.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:07.220859+00:00
-- url     : https://prove2.me/submissions/0bbd444a-3883-44b6-b6b6-db686f34f703

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData46Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared46_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared46.right_signatures_checked





end D1Bound5.PairLightPrepared46
end
