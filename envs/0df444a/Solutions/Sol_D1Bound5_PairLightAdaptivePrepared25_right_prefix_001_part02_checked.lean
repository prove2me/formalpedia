-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:09.878985+00:00
-- url     : https://prove2.me/submissions/64ae7914-342a-4e9c-9493-2e9e74323100

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 209 through 272, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 64
      (rightCached001.drop 84) (rightRows001.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
