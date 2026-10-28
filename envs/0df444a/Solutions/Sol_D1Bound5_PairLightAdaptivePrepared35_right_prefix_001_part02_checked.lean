-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:08.625927+00:00
-- url     : https://prove2.me/submissions/2e0361e2-72ae-4420-be39-d485bee61078

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 242 through 367; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 126
      (rightCached001.drop 110) (rightRows001.drop 110) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
