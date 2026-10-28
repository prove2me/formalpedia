-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:50.298278+00:00
-- url     : https://prove2.me/submissions/99a8ea53-0173-449c-b2ec-5181a7ed96de

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared30.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared30.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared30
end
