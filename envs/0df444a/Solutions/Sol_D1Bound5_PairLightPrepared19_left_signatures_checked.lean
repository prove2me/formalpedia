-- Prove2me | solution 1 for D1Bound5.PairLightPrepared19.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:19:23.020436+00:00
-- url     : https://prove2.me/submissions/05e096a2-bd50-479d-93df-888a111a7292

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared19_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared19.left_signatures_checked





end D1Bound5.PairLightPrepared19
end
