-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:13:34.783677+00:00
-- url     : https://prove2.me/submissions/5766c8d8-f732-4697-83f5-46b393ebc1de

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared28.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared28.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared28
end
