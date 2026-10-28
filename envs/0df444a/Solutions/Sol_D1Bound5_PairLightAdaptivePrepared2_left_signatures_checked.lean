-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared2.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:26:03.824232+00:00
-- url     : https://prove2.me/submissions/44e8561e-059c-42b3-883c-53cbbe5ded9d

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData2_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared2
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared2.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared2.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared2
end
