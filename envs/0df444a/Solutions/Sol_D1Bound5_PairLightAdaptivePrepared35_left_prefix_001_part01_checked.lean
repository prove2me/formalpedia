-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:57.325202+00:00
-- url     : https://prove2.me/submissions/7bbc3b71-4ee3-47da-a341-39f78ba0c8ca

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 178 through 239; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 62
      (leftCached001.drop 46) (leftRows001.drop 46) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
