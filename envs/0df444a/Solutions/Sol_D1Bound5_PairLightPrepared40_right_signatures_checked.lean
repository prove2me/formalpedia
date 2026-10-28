-- Prove2me | solution 1 for D1Bound5.PairLightPrepared40.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:32:11.926094+00:00
-- url     : https://prove2.me/submissions/f35178b6-b3a8-48d1-bc69-93952ccee133

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_signatures_checked

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (rightCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared40.right_signatures_checked





end D1Bound5.PairLightPrepared40
end
