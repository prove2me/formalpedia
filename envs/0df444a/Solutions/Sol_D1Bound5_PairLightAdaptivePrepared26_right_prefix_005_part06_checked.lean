-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:27.022377+00:00
-- url     : https://prove2.me/submissions/66633ee1-c49e-4b9e-89f3-9bf3e588da89

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 408 through 419; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached005.drop 72) (rightRows005.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
