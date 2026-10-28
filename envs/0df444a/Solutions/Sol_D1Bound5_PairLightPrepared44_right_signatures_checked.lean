-- Prove2me | solution 1 for D1Bound5.PairLightPrepared44.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:08.417555+00:00
-- url     : https://prove2.me/submissions/28ea2351-1f9a-4dfc-843f-7947f09cf3f8

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared44.right_signatures_checked





end D1Bound5.PairLightPrepared44
end
