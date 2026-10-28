-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:17.55553+00:00
-- url     : https://prove2.me/submissions/f7fd7575-3a59-47e6-8500-7f7b91b1424b

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared7.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared7.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared7
end
