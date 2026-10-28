-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:26.753966+00:00
-- url     : https://prove2.me/submissions/c3cbcd7c-3a0c-4219-b030-821a7566f03e

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared5.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared5.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared5
end
