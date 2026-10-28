-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:59.483459+00:00
-- url     : https://prove2.me/submissions/b1b0b227-3066-425b-892a-e19d15ddbdfa

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_005

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared17.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared17.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared17
end
