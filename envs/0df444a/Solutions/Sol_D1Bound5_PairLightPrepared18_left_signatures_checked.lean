-- Prove2me | solution 1 for D1Bound5.PairLightPrepared18.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:23:00.684993+00:00
-- url     : https://prove2.me/submissions/4314c0af-ae5e-4b5e-88e5-c8d577aebe9f

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared18.left_signatures_checked





end D1Bound5.PairLightPrepared18
end
