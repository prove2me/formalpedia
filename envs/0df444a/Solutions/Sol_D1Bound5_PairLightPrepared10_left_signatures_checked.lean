-- Prove2me | solution 1 for D1Bound5.PairLightPrepared10.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:16.211271+00:00
-- url     : https://prove2.me/submissions/4d1d02c7-f151-4ab6-a2c9-00df16ba1bb9

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared10_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared10.left_signatures_checked





end D1Bound5.PairLightPrepared10
end
