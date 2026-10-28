-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:17.927977+00:00
-- url     : https://prove2.me/submissions/b7735762-63c7-4b84-be44-0947819f5a93

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared14.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared14.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared14
end
