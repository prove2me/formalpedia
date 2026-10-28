-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:31.031832+00:00
-- url     : https://prove2.me/submissions/d98a796a-6fe5-4310-b84b-8660e0244a07

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 50 through 77, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 28
      (rightCached000.drop 50) (rightRows000.drop 50) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
