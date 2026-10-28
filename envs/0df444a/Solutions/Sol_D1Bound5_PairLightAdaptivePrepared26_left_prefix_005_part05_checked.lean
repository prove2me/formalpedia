-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:36.953994+00:00
-- url     : https://prove2.me/submissions/c15c46d1-f9bd-4702-a0cd-68042a4804ee

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 396 through 407; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached005.drop 60) (leftRows005.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
