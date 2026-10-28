-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:24:02.46081+00:00
-- url     : https://prove2.me/submissions/4c67b0fa-2238-4918-a202-553fe601bb3b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 82 through 107, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 26
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared11
end
