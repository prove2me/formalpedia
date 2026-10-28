-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:24:03.4068+00:00
-- url     : https://prove2.me/submissions/70f3ab9e-91fa-4503-aeeb-2afd031f442c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 172 through 213, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 42
      (rightCached001.drop 34) (rightRows001.drop 34) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
