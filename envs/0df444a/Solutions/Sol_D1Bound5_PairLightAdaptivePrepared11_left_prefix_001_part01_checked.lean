-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:19.927152+00:00
-- url     : https://prove2.me/submissions/cea462a6-75f4-45c4-883e-8c20be4b59e9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 172 through 213, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 42
      (leftCached001.drop 34) (leftRows001.drop 34) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared11
end
