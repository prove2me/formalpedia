-- Prove2me | solution 1 for D1Bound5.PairLightPrepared33.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:15:05.64809+00:00
-- url     : https://prove2.me/submissions/e7bc4ea8-3a88-4c34-8aa1-7af33a492faf

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared33_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared33.left_signatures_checked





end D1Bound5.PairLightPrepared33
end
