-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared45.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:18.595982+00:00
-- url     : https://prove2.me/submissions/33784d57-0648-4e37-b3eb-4bb0a3b09535

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (PairLightPrepared45.leftCached.all fun x =>
      decide (x.2 = pairLightCoordinateSignature PairLightPrepared45.sieve x.1)) = true := by
  decide +kernel






end D1Bound5.PairLightAdaptivePrepared45
end
