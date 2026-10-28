-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_000_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:15.429361+00:00
-- url     : https://prove2.me/submissions/9c131e53-c954-4269-b252-ac2e0604bd02

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 18 through 20 of the original first block; every full tail is retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached000.drop 18) (rightRows000.drop 18) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
