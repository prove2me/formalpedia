-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared42.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:53.285908+00:00
-- url     : https://prove2.me/submissions/a4e08349-e7c4-4e5e-8754-7b92fe0a10d6

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData42_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 241; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared42.sieve 242
      rightCached000 rightRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared42
end
