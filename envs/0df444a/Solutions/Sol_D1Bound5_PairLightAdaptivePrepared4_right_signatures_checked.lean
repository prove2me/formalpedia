-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:50:02.312912+00:00
-- url     : https://prove2.me/submissions/7aed0631-3d36-4b81-b03e-b182d9c01bb4

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared4.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared4.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared4
end
