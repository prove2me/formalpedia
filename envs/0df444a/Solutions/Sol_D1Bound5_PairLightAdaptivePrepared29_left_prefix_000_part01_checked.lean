-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:49:53.440647+00:00
-- url     : https://prove2.me/submissions/9c7773a7-51d7-42fa-a825-385ec31fcf5f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 24 through 49, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 26
      (leftCached000.drop 24) (leftRows000.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
