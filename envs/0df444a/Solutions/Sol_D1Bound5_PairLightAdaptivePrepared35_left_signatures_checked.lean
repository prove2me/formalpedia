-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:00.400771+00:00
-- url     : https://prove2.me/submissions/6fc74e64-86c0-4516-aee0-db4d19ba68fe

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared35.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared35.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared35
end
