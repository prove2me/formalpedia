-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:20.725622+00:00
-- url     : https://prove2.me/submissions/7763cdd0-a9d0-4bfe-9795-139dd2e8605b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 136 through 137; every head retains its complete original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 2
      (leftCached000.drop 136) (leftRows000.drop 136) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared12
end
