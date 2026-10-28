-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_006_part14_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:59.842417+00:00
-- url     : https://prove2.me/submissions/c0264edf-d924-4335-b086-17b0d816e0dd

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 611 through 615; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 5
      (rightCached006.drop 168) (rightRows006.drop 168) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
