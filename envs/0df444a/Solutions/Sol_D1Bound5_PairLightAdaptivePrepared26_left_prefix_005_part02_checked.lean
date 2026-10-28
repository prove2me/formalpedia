-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:16.803954+00:00
-- url     : https://prove2.me/submissions/a2795a63-397a-47da-88a7-54432fb13958

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 360 through 371; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached005.drop 24) (leftRows005.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
