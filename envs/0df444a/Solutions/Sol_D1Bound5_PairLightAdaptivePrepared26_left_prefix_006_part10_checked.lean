-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_006_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:50.051002+00:00
-- url     : https://prove2.me/submissions/52e024b7-fea5-4120-9634-a7c9b44b6d0c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 563 through 574; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached006.drop 120) (leftRows006.drop 120) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
