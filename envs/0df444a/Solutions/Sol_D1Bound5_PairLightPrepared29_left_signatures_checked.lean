-- Prove2me | solution 1 for D1Bound5.PairLightPrepared29.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:04.852832+00:00
-- url     : https://prove2.me/submissions/1b381e90-deeb-408a-9e0d-41b7f4ded8ce

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared29.left_signatures_checked





end D1Bound5.PairLightPrepared29
end
