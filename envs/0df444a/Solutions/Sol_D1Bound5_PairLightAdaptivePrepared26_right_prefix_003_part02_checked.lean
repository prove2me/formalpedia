-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:48.992354+00:00
-- url     : https://prove2.me/submissions/55b12734-3049-45a9-83bf-f8116826f149

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 202 through 213; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached003.drop 24) (rightRows003.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
