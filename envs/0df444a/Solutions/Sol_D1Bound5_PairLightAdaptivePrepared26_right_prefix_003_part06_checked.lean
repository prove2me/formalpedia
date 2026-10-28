-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:17.973476+00:00
-- url     : https://prove2.me/submissions/5bb2dfce-8275-490d-b25c-0bfe53c22ba3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 250 through 250; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (rightCached003.drop 72) (rightRows003.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
