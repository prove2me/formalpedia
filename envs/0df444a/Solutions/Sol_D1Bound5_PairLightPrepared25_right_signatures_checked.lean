-- Prove2me | solution 1 for D1Bound5.PairLightPrepared25.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:33:27.963134+00:00
-- url     : https://prove2.me/submissions/57314c91-e7e9-4215-bd8e-1523960683ee

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared25.right_signatures_checked





end D1Bound5.PairLightPrepared25
end
