-- Prove2me | solution 1 for D1Bound5.PairLightPrepared17.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:25.369194+00:00
-- url     : https://prove2.me/submissions/6bff240b-613e-4b2b-b46d-71aeab769af9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared17.right_signatures_checked





end D1Bound5.PairLightPrepared17
end
