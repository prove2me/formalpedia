-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:09.882356+00:00
-- url     : https://prove2.me/submissions/84b97e1e-6c4d-4061-9b6d-9a12c822e481

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 109 through 125, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 17
      (leftCached000.drop 109) (leftRows000.drop 109) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
