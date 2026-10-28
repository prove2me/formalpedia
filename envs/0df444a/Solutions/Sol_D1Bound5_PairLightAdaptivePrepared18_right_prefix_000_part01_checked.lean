-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:42.602236+00:00
-- url     : https://prove2.me/submissions/b8e2d12a-e4a0-4320-9e3b-7564fc3fafad

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 35 through 76; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 42
      (rightCached000.drop 35) (rightRows000.drop 35) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared18
end
