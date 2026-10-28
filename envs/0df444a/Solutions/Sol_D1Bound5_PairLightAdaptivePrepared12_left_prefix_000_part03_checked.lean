-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:17.24399+00:00
-- url     : https://prove2.me/submissions/cf7576c8-8cba-425b-9044-ba5f442d42c7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 95 through 135; every head retains its complete original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 41
      (leftCached000.drop 95) (leftRows000.drop 95) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared12
end
