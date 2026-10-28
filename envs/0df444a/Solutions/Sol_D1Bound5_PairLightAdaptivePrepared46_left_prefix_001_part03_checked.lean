-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:26.406161+00:00
-- url     : https://prove2.me/submissions/dbf7b92f-6d80-43be-accf-fc9050106ed1

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 269 through 359, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 91
      (leftCached001.drop 132) (leftRows001.drop 132) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
