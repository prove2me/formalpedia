-- Prove2me | solution 1 for D1Bound5.PairLightPrepared3.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:14:59.386316+00:00
-- url     : https://prove2.me/submissions/a78dabd7-aa15-476c-b5a7-5d77feb2451a

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared3.left_signatures_checked





end D1Bound5.PairLightPrepared3
end
