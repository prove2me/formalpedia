-- Prove2me | solution 1 for D1Bound5.PairLightPrepared21.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:29:25.488732+00:00
-- url     : https://prove2.me/submissions/f7e5f905-8834-41a3-8f22-3cb48316c821

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared21.right_signatures_checked





end D1Bound5.PairLightPrepared21
end
