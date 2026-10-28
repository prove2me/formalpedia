-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:46:03.602998+00:00
-- url     : https://prove2.me/submissions/60ee73fb-73b8-4570-b4b6-e397c67da7bf

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared23.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared23.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared23
end
