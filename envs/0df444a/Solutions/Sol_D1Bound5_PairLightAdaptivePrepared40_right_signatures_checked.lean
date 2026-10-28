-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.right_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:51:09.278796+00:00
-- url     : https://prove2.me/submissions/02cf17b9-6287-4618-b394-3acf3a32cd0c

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_004

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0







theorem _root_.solution :
    (PairLightPrepared40.rightCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared40.sieve x.1)) = true := by
  decide +kernel


end D1Bound5.PairLightAdaptivePrepared40
end
