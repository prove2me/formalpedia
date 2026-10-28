-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:26.091605+00:00
-- url     : https://prove2.me/submissions/a50fad65-66d2-4514-ab69-859c64e676e9

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared17.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared17.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared17
end
