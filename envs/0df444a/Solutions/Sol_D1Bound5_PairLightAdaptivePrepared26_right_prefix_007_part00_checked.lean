-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:51.648088+00:00
-- url     : https://prove2.me/submissions/c694cc00-ce47-4841-a11b-7851143cde8c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 616 through 627; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached007.drop 0) (rightRows007.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
