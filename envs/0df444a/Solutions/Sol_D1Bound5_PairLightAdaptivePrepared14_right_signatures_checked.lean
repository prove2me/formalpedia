-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:20.933281+00:00
-- url     : https://prove2.me/submissions/b14c67b3-34a4-492e-93a9-06d486941b80

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared14.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared14.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared14
end
