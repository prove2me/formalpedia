-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:17:03.143727+00:00
-- url     : https://prove2.me/submissions/dc3184e3-3839-43fa-b52c-8a5989a46d74

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 29 through 60; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 32
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
