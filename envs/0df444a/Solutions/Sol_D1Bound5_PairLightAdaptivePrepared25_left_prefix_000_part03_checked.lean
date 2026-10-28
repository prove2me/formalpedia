-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:57.757386+00:00
-- url     : https://prove2.me/submissions/af16a0fb-ac65-4d9c-9cd2-6bfa3a1c4d9d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 78 through 108, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 31
      (leftCached000.drop 78) (leftRows000.drop 78) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
