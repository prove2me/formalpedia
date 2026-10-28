-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:06.943332+00:00
-- url     : https://prove2.me/submissions/9c6fa091-5f62-43dc-bd86-723001276ab5

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 238 through 249; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached003.drop 60) (leftRows003.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
