-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:45.465986+00:00
-- url     : https://prove2.me/submissions/6a222b87-1528-42bc-8ee7-efdeb6fe53b6

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 24 through 49, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 26
      (rightCached000.drop 24) (rightRows000.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
