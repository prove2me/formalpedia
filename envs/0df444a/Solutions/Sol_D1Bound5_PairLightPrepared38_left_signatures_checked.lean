-- Prove2me | solution 1 for D1Bound5.PairLightPrepared38.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:04.593911+00:00
-- url     : https://prove2.me/submissions/32ff9e83-f858-4c03-95a9-fb143d1c10da

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared38.left_signatures_checked





end D1Bound5.PairLightPrepared38
end
