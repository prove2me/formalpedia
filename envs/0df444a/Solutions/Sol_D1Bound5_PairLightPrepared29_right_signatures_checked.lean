-- Prove2me | solution 1 for D1Bound5.PairLightPrepared29.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:11.165015+00:00
-- url     : https://prove2.me/submissions/0f568ed0-f77b-4d46-a8ed-085f8608ec74

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData29Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared29.right_signatures_checked





end D1Bound5.PairLightPrepared29
end
