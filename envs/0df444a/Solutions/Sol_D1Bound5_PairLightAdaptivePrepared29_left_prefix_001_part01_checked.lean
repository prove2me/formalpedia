-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:58.145809+00:00
-- url     : https://prove2.me/submissions/76b5ce66-aee5-401b-b3a4-6174e14dd882

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 164 through 209, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 46
      (leftCached001.drop 38) (leftRows001.drop 38) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
