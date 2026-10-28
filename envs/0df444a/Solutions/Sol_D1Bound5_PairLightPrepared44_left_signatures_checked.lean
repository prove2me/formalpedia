-- Prove2me | solution 1 for D1Bound5.PairLightPrepared44.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:12.162303+00:00
-- url     : https://prove2.me/submissions/a9b2e9b3-96e3-4d04-a2d8-1207fb6e2c10

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared44_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared44.left_signatures_checked





end D1Bound5.PairLightPrepared44
end
