-- Prove2me | solution 1 for D1Bound5.PairLightPrepared3.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:19.527452+00:00
-- url     : https://prove2.me/submissions/94182072-725a-4324-9a8e-9316e9fdbb36

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared3.right_signatures_checked





end D1Bound5.PairLightPrepared3
end
