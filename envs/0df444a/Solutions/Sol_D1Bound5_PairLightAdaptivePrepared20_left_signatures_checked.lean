-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared20.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:56:35.59185+00:00
-- url     : https://prove2.me/submissions/ca3f5f03-afb0-40e4-8fae-30474e6a17ae

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared20.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared20.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared20
end
