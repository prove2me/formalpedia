-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:02.147254+00:00
-- url     : https://prove2.me/submissions/778180d9-50ac-4a71-924d-c6ce054a422b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 336 through 347; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached005.drop 0) (rightRows005.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
