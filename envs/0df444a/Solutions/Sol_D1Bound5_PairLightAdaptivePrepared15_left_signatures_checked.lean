-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:56:37.571332+00:00
-- url     : https://prove2.me/submissions/b6f157ee-2f5d-4d45-b4ed-3f6b456e019c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared15.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared15.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared15
end
