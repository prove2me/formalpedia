-- Prove2me | solution 1 for D1Bound5.PairLightPrepared25.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:30:58.295403+00:00
-- url     : https://prove2.me/submissions/e2788dfd-c8e6-482e-bd2f-b4ffb8eceda2

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared25_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared25.left_signatures_checked





end D1Bound5.PairLightPrepared25
end
