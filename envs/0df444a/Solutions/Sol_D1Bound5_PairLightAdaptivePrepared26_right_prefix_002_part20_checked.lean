-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part20_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:13.218596+00:00
-- url     : https://prove2.me/submissions/1e3d1334-9cfe-49f3-baaf-88a3dff69039

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 173 through 175; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 60) (rightRows002.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
