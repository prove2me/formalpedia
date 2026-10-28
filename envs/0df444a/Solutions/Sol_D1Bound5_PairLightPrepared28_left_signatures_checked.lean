-- Prove2me | solution 1 for D1Bound5.PairLightPrepared28.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:49.693665+00:00
-- url     : https://prove2.me/submissions/892c8581-f5a2-4855-b44b-c6a771838010

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared28.left_signatures_checked





end D1Bound5.PairLightPrepared28
end
