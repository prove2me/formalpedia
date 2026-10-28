-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared13.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:03:10.49579+00:00
-- url     : https://prove2.me/submissions/7976a43c-be6d-4afa-8799-afa62292e3ca

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData13_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData13_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 247; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared13.sieve 248
      leftCached000 leftRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared13
end
