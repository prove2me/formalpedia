-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:52.723336+00:00
-- url     : https://prove2.me/submissions/6b687d9a-702c-47a5-84ef-2ba28b34321a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 16 through 35, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 20
      (leftCached000.drop 16) (leftRows000.drop 16) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
