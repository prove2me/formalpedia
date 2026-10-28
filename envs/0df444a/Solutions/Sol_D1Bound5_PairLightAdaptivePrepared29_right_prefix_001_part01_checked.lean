-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:49.928721+00:00
-- url     : https://prove2.me/submissions/47fc7909-afb4-46ef-b7a4-73c319f70db0

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 163 through 208, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 46
      (rightCached001.drop 38) (rightRows001.drop 38) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
