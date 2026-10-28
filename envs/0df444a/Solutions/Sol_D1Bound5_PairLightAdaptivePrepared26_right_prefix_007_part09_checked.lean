-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_007_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:25.70814+00:00
-- url     : https://prove2.me/submissions/50d75b7c-4493-499d-9026-04b1c99c602b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 724 through 735; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached007.drop 108) (rightRows007.drop 108) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
