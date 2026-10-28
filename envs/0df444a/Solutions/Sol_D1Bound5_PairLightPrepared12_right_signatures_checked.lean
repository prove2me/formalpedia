-- Prove2me | solution 1 for D1Bound5.PairLightPrepared12.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:18:16.351083+00:00
-- url     : https://prove2.me/submissions/045ac698-9544-4998-86be-bfdf1c1808fd

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_005
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared12.right_signatures_checked





end D1Bound5.PairLightPrepared12
end
