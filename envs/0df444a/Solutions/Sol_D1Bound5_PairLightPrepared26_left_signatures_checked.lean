-- Prove2me | solution 1 for D1Bound5.PairLightPrepared26.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:28:09.122981+00:00
-- url     : https://prove2.me/submissions/7688bf04-eda9-4a90-b2d5-a8ac20518c9a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_003
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared26.left_signatures_checked





end D1Bound5.PairLightPrepared26
end
