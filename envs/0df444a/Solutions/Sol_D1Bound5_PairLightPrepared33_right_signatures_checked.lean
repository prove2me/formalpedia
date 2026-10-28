-- Prove2me | solution 1 for D1Bound5.PairLightPrepared33.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:18.685463+00:00
-- url     : https://prove2.me/submissions/9412d8d2-e8f4-4309-97f9-9430eff70d04

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared33.right_signatures_checked





end D1Bound5.PairLightPrepared33
end
