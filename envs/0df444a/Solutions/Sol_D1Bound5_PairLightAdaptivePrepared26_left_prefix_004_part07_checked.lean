-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_004_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:47.400374+00:00
-- url     : https://prove2.me/submissions/113dfb6b-b2ca-4923-9e3d-688f179cdabf

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 335 through 335; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (leftCached004.drop 84) (leftRows004.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
