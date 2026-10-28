-- Prove2me | solution 1 for D1Bound5.PairLightPrepared8.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:08.35898+00:00
-- url     : https://prove2.me/submissions/de7f70b2-c022-4a3a-8315-b751a5db40bf

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared8_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared8
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared8.right_signatures_checked





end D1Bound5.PairLightPrepared8
end
