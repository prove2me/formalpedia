-- Prove2me | solution 1 for D1Bound5.PairLightPrepared24.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:26.934156+00:00
-- url     : https://prove2.me/submissions/af144002-d179-4b59-ae61-144961605a8f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared24.right_signatures_checked





end D1Bound5.PairLightPrepared24
end
