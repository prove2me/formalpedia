-- Prove2me | solution 1 for D1Bound5.PairLightPrepared23.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:39:45.827665+00:00
-- url     : https://prove2.me/submissions/7eebd1e2-c041-49be-a9fb-10e8a0d84362

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared23.right_signatures_checked





end D1Bound5.PairLightPrepared23
end
