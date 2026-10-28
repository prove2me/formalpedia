-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:51.525175+00:00
-- url     : https://prove2.me/submissions/e919e6cf-8148-4efa-8da8-ca04decbb852

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared24.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared24.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared24
end
