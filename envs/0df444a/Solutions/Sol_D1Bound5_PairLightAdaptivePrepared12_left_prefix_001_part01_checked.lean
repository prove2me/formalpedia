-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:48.109983+00:00
-- url     : https://prove2.me/submissions/3cd66012-f387-46d7-9728-7eb856966092

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 189 through 264; every head retains its complete original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 76
      (leftCached001.drop 51) (leftRows001.drop 51) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared12
end
