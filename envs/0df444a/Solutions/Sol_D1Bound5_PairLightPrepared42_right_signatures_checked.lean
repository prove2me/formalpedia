-- Prove2me | solution 1 for D1Bound5.PairLightPrepared42.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:14:57.688647+00:00
-- url     : https://prove2.me/submissions/9ecb8694-fd96-4bb8-9ec0-be3c1cf9f6e5

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared42_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared42.right_signatures_checked





end D1Bound5.PairLightPrepared42
end
