-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared42.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:52.682835+00:00
-- url     : https://prove2.me/submissions/4e36b33e-2fa2-4a85-b744-879c7c1ead7e

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
      leftCached000 leftRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared42
end
