-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:58.847328+00:00
-- url     : https://prove2.me/submissions/ae43456c-22a1-400f-9e5f-d5fa158c9f6f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 214 through 269, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 56
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared11
end
