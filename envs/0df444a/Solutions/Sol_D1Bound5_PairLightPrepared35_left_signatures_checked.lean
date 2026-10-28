-- Prove2me | solution 1 for D1Bound5.PairLightPrepared35.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:26:15.430927+00:00
-- url     : https://prove2.me/submissions/b2073d1c-5adb-49bd-a6df-5b46caac406a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared35.left_signatures_checked





end D1Bound5.PairLightPrepared35
end
