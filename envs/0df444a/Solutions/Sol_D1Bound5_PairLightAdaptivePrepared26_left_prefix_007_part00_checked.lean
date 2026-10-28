-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:36:43.01522+00:00
-- url     : https://prove2.me/submissions/aea94f4f-ab98-4f7e-962f-194c124d41e2

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 616 through 627; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached007.drop 0) (leftRows007.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
