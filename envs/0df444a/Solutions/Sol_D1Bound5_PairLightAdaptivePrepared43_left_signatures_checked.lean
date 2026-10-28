-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:52.362422+00:00
-- url     : https://prove2.me/submissions/69500d8e-039f-479a-99ba-b09d7c113d25

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared43.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared43.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared43
end
