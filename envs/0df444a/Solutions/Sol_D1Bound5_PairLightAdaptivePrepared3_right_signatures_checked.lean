-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:20.45999+00:00
-- url     : https://prove2.me/submissions/80cf58bb-ed57-4a0a-ae31-8d4b149bcc90

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared3.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared3.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared3
end
