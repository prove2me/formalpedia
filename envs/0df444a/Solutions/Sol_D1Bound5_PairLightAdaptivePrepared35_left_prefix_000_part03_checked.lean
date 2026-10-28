-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:30.863539+00:00
-- url     : https://prove2.me/submissions/6b3ae70d-cecc-491a-8570-0c779bd96180

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 92 through 129; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 38
      (leftCached000.drop 92) (leftRows000.drop 92) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
