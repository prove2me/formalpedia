-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:08.345989+00:00
-- url     : https://prove2.me/submissions/a9b014e2-3854-4fa4-a0fa-be0ba528dd4b

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared19.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared19.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared19
end
