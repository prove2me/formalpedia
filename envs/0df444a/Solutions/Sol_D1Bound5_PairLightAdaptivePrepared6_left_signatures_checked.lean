-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:20:00.376247+00:00
-- url     : https://prove2.me/submissions/1c5f0e15-3f70-4700-b920-49ff16de6bc8

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared6.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared6.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared6
end
