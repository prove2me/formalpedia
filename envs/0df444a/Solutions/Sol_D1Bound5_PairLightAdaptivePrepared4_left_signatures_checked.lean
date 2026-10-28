-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:46.842986+00:00
-- url     : https://prove2.me/submissions/34632801-6fa6-44e7-86ee-db183acf2c23

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared4.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared4.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared4
end
