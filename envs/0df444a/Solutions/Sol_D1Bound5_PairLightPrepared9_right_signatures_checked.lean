-- Prove2me | solution 1 for D1Bound5.PairLightPrepared9.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:26.290399+00:00
-- url     : https://prove2.me/submissions/72dfed46-adc8-4bb3-9a3a-9e83363b1484

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared9.right_signatures_checked





end D1Bound5.PairLightPrepared9
end
