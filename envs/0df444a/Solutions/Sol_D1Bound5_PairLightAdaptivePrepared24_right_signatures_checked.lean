-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:08.669383+00:00
-- url     : https://prove2.me/submissions/5fb10daf-64a4-47e1-a3f7-e4f124e7bbfd

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared24.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared24.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared24
end
