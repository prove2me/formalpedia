-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:45.866297+00:00
-- url     : https://prove2.me/submissions/aa36d001-ccee-4454-bb0d-d6c3c540c469

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 172 through 213, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 42
      (rightCached001.drop 34) (rightRows001.drop 34) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
