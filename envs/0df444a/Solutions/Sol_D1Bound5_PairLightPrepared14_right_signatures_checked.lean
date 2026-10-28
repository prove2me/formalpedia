-- Prove2me | solution 1 for D1Bound5.PairLightPrepared14.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:28.660439+00:00
-- url     : https://prove2.me/submissions/f1f14c1f-c1cc-4169-89c3-d89b93ce00ca

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared14.right_signatures_checked





end D1Bound5.PairLightPrepared14
end
