-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:13.923227+00:00
-- url     : https://prove2.me/submissions/826cbd78-8928-4679-a47f-97c3102de977

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 563 through 574; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached006.drop 120) (rightRows006.drop 120) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
