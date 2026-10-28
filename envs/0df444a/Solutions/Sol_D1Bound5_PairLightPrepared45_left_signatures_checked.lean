-- Prove2me | solution 1 for D1Bound5.PairLightPrepared45.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:22.710569+00:00
-- url     : https://prove2.me/submissions/9a8663b9-2338-426b-ad07-c579bce50417

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared45_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared45.left_signatures_checked





end D1Bound5.PairLightPrepared45
end
