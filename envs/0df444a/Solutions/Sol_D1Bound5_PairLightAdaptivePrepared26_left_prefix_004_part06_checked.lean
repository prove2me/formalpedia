-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:19.230327+00:00
-- url     : https://prove2.me/submissions/22c13b3c-331f-4e23-90e7-850b2d4f8495

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 323 through 334; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached004.drop 72) (leftRows004.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
