-- Prove2me | solution 1 for D1Bound5.PairLightPrepared1.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:13.027764+00:00
-- url     : https://prove2.me/submissions/1048fe30-9d06-4edc-bd79-df2343c7a03e

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared1.right_signatures_checked





end D1Bound5.PairLightPrepared1
end
