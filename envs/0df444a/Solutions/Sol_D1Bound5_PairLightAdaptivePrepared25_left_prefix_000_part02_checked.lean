-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:25.886274+00:00
-- url     : https://prove2.me/submissions/9b3d7aa8-8b07-4741-9196-f8294d907224

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
      (leftCached000.drop 50) (leftRows000.drop 50) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
