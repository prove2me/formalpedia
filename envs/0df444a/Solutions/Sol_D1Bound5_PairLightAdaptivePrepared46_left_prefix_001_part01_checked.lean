-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:52.785243+00:00
-- url     : https://prove2.me/submissions/957886b1-7769-434e-b3d3-fe2c9229875e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 171 through 212, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 42
      (leftCached001.drop 34) (leftRows001.drop 34) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
