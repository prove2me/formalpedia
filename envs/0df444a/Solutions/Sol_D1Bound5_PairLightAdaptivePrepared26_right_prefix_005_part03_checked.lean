-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_005_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:41.400009+00:00
-- url     : https://prove2.me/submissions/0d57bbc1-9e26-4c40-9a5c-0e1f153e5676

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 372 through 383; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached005.drop 36) (rightRows005.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
