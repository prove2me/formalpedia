-- Prove2me | solution 1 for D1Bound5.PairLightPrepared26.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:18:15.543019+00:00
-- url     : https://prove2.me/submissions/848fdc0f-c076-462a-bbd1-027f68983dcb

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_008
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared26.right_signatures_checked





end D1Bound5.PairLightPrepared26
end
