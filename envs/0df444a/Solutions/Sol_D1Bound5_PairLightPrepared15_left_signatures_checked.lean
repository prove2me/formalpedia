-- Prove2me | solution 1 for D1Bound5.PairLightPrepared15.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:25.34591+00:00
-- url     : https://prove2.me/submissions/ea02620d-b260-49da-8da7-0425d8ee7cee

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared15.left_signatures_checked





end D1Bound5.PairLightPrepared15
end
