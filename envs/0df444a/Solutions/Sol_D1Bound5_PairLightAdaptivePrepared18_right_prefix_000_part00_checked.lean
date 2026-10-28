-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:57.484636+00:00
-- url     : https://prove2.me/submissions/65e93670-888b-4b71-aee2-b23025144cb2

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 0 through 34; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 35
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared18
end
