-- Prove2me | solution 1 for D1Bound5.PairLightPrepared48.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:01.350435+00:00
-- url     : https://prove2.me/submissions/67a7651d-8b61-44f0-a490-3315211d03a5

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData48Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared48.right_signatures_checked





end D1Bound5.PairLightPrepared48
end
