-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:15.213301+00:00
-- url     : https://prove2.me/submissions/297edbb8-0a6d-4282-8887-57b968d977f8

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared10.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared10.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared10
end
