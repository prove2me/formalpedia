-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:13.801341+00:00
-- url     : https://prove2.me/submissions/418b94c4-3b92-4973-9a02-4cb13618dcf8

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
      (leftCached000.drop 24) (leftRows000.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
