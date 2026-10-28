-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:43.683462+00:00
-- url     : https://prove2.me/submissions/f10bc9f8-8afa-4d53-ad62-123cf6295925

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared7.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared7.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared7
end
