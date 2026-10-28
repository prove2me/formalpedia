-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:29.30458+00:00
-- url     : https://prove2.me/submissions/91a0302e-6ae2-4643-b38f-f34eebc2d9ee

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 287 through 298; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached004.drop 36) (leftRows004.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
