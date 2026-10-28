-- Prove2me | solution 1 for D1Bound5.PairLightPrepared43.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:22.755549+00:00
-- url     : https://prove2.me/submissions/44897995-9682-4bbb-91af-874b1a6b9c8f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared43_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared43.left_signatures_checked





end D1Bound5.PairLightPrepared43
end
