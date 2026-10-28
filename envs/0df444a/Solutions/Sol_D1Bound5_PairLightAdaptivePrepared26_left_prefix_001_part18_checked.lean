-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part18_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:44.323702+00:00
-- url     : https://prove2.me/submissions/c4ba5722-4521-4488-93ef-19f727310f39

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 108 through 110; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached001.drop 54) (leftRows001.drop 54) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
