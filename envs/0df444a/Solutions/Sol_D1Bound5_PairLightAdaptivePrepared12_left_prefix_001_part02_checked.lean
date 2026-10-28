-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:33.396574+00:00
-- url     : https://prove2.me/submissions/8a8f5bc1-12d5-4a9e-9185-99ab3c47601f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 265 through 358; every head retains its complete original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 94
      (leftCached001.drop 127) (leftRows001.drop 127) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared12
end
