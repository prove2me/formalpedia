-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:35.195464+00:00
-- url     : https://prove2.me/submissions/29e76e79-3bbd-48f1-b164-c729d494953f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 273 through 380, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 108
      (rightCached001.drop 148) (rightRows001.drop 148) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
